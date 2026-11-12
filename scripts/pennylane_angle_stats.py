"""Per-setting check of PennyLane's GQSP angles for the LCU run (results/pennylane_lcu.csv).

PennyLane's estimator (GQSPTimeEvolution) never computes angles. Here, for each
(program, error, time), we build the polynomial it assumes and run PennyLane's
angle solver on it, then evaluate the circuit those angles define:

  pl     PennyLane's own degree N (poly_approx) and the Jacobi-Anger polynomial
         as is, P(z) = z^N sum_{|k|<=N} (-i)^|k| J_|k|(tau) z^k, tau = lambda t
         (what a user would pass to qml.poly_to_angles(P, "GQSP")).
  valid  A correctly budgeted PennyLane run: the smallest degree whose true
         truncation error is <= eps/4 (exact_degree, by FFT), P rescaled to
         max |P| = 1 - eps/4 on the unit circle (QBlue's QSP margin for one
         segment), which costs <= ~eps/2, leaving ~eps/4 for the angles. Passed
         as is (pl), P slightly exceeds 1 and poly_to_angles rejects it; with a
         margin of ~1e-9 its root split still fails.

For each: status (ok, crash, or too_large when 2N > --max-degree; PennyLane's
complementary-polynomial step finds the roots of a degree-4N polynomial through
a dense companion matrix, which needs ~16 (4N)^2 bytes), the total error
max_theta |<0|GQSP(angles)|0> - e^{iN theta} e^{-i tau cos theta}| (what the
simulation gets; compare with eps), and the solver error max |<0|GQSP|0> - P|.

  ~/pl-venv/bin/python scripts/pennylane_angle_stats.py --workers 4
writes results/pennylane_angle_stats.csv and prints a summary.
"""

import argparse
import csv
import math
import os
import sys
import time
import warnings
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
from scipy.special import jv

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
FIELDS = ["file_name", "error", "time", "tau", "pl_degree", "exact_degree",
          "pl_status", "pl_total_error", "pl_solver_error", "pl_seconds",
          "valid_status", "valid_total_error", "valid_solver_error", "valid_seconds", "message"]


def jacobi_anger(tau, N):
    """coefficients of z^0..z^{2N} for z^N e^{-i tau cos theta}, truncated at |k| <= N"""
    k = np.arange(-N, N + 1)
    return (-1j) ** (np.abs(k) % 4) * jv(np.abs(k), tau)


def gqsp_values(angles, zs):
    """<0| GQSP |0> with the signal unitary acting as z, following
    qml.GQSP.compute_decomposition: X U3(2 th, ph, la) X Z per layer, 0-controlled U between"""
    th, ph, la = np.asarray(angles)
    m00 = np.ones_like(zs); m01 = np.zeros_like(zs); m10 = np.zeros_like(zs); m11 = np.ones_like(zs)

    def left(A, m00, m01, m10, m11):
        return (A[0, 0] * m00 + A[0, 1] * m10, A[0, 0] * m01 + A[0, 1] * m11,
                A[1, 0] * m00 + A[1, 1] * m10, A[1, 0] * m01 + A[1, 1] * m11)

    X = np.array([[0, 1], [1, 0]]); Z = np.diag([1, -1])

    def layer(t, p, l):
        c, s = np.cos(t), np.sin(t)       # U3(2t, p, l)
        u = np.array([[c, -np.exp(1j * l) * s], [np.exp(1j * p) * s, np.exp(1j * (p + l)) * c]])
        return Z @ X @ u @ X

    m00, m01, m10, m11 = left(layer(th[0], ph[0], la[0]), m00, m01, m10, m11)
    for t, p, l in zip(th[1:], ph[1:], la[1:]):
        m00, m01 = zs * m00, zs * m01          # 0-controlled U: z on the |0> row
        m00, m01, m10, m11 = left(layer(t, p, l), m00, m01, m10, m11)
    return m00


def run_one(poly, tau, N, max_degree):
    import pennylane as qml
    d = len(poly) - 1
    if d > max_degree:
        return dict(status="too_large", seconds=0.0,
                    message=f"degree {d}: companion matrix ~{16 * (2 * d) ** 2 / 1e9:.0f} GB")
    G = 1 << int(math.ceil(math.log2(8 * (d + 1))))
    zs = np.exp(2j * np.pi * np.arange(G) / G)
    t0 = time.time()
    try:
        ang = qml.poly_to_angles(poly, "GQSP")
    except Exception as e:
        return dict(status="crash", seconds=time.time() - t0, message=f"{type(e).__name__}: {str(e)[:100]}")
    secs = time.time() - t0
    got = gqsp_values(ang, zs)
    exact = zs ** N * np.exp(-1j * tau * zs.real)
    want = np.polynomial.polynomial.polyval(zs, poly)
    if not np.all(np.isfinite(got)):
        return dict(status="crash", seconds=secs, message="non-finite angles")
    return dict(status="ok", seconds=secs, total=float(np.abs(got - exact).max()),
                solver=float(np.abs(got - want).max()))


def job(row, max_degree):
    import pennylane_lcu as P
    tau = float(row["one_norm"]) * float(row["time"])
    N_pl = int(row["poly_degree"]) // 2
    N_ex = int(row["exact_degree"]) // 2
    out = dict(file_name=row["file_name"], error=row["error"], time=row["time"], tau=tau,
               pl_degree=2 * N_pl, exact_degree=2 * N_ex, message="")
    a = run_one(jacobi_anger(tau, N_pl), tau, N_pl, max_degree)
    # error budget: truncation <= eps/4, rescaling <= ~eps/2, angles the rest
    N_ex = P.exact_degree(tau, float(row["error"]) / 4, N_ex)
    out["exact_degree"] = 2 * N_ex
    poly = jacobi_anger(tau, N_ex)
    # margin eps/4 below 1, as QBlue's QSP uses (1 - eps/(4r)) with r = 1:
    # with |P| within ~1e-9 of 1 PennyLane's root split fails as well
    G = 1 << int(math.ceil(math.log2(16 * (2 * N_ex + 1))))
    mx = np.abs(np.polynomial.polynomial.polyval(np.exp(2j * np.pi * np.arange(G) / G), poly)).max()
    poly = poly * (1 - float(row["error"]) / 4) / mx
    b = run_one(poly, tau, N_ex, max_degree)
    for key, r in (("pl", a), ("valid", b)):
        out[f"{key}_status"] = r["status"]
        out[f"{key}_total_error"] = r.get("total", "")
        out[f"{key}_solver_error"] = r.get("solver", "")
        out[f"{key}_seconds"] = round(r["seconds"], 3)
        if r.get("message"):
            out["message"] += f"{key}: {r['message']}; "
    return out


def main():
    warnings.filterwarnings("ignore")
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--input", default=str(ROOT / "results/pennylane_lcu.csv"))
    ap.add_argument("--output", default=str(ROOT / "results/pennylane_angle_stats.csv"))
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--max-degree", type=int, default=3300)
    args = ap.parse_args()

    rows = {}
    for r in csv.DictReader(open(args.input)):
        key = (r["file_name"], r["error"], r["time"])
        if r["method"] == "pl_est":
            rows.setdefault(key, {}).update(r)
        elif r["method"] == "pl_est_exact":
            rows.setdefault(key, {})["exact_degree"] = r["poly_degree"]
    jobs = [r for r in rows.values() if "poly_degree" in r and "exact_degree" in r]
    jobs.sort(key=lambda r: -int(r["poly_degree"]))       # largest first
    out = []
    with ProcessPoolExecutor(args.workers) as pool:
        futs = [pool.submit(job, r, args.max_degree) for r in jobs]
        for i, f in enumerate(as_completed(futs), 1):
            out.append(f.result())
            if i % 50 == 0 or i == len(futs):
                print(f"[{i}/{len(futs)}]", flush=True)
                with open(args.output, "w", newline="") as fh:
                    w = csv.DictWriter(fh, FIELDS)
                    w.writeheader()
                    w.writerows(sorted(out, key=lambda r: (r["file_name"], float(r["error"]), float(r["time"]))))
    summarize(out)


def summarize(out):
    n = len(out)
    for key, label in (("pl", "PennyLane as used (its degree, polynomial as is)"),
                       ("valid", "Solver alone (degree that meets eps, valid input)")):
        st = [r[f"{key}_status"] for r in out]
        ok = [r for r in out if r[f"{key}_status"] == "ok"]
        meets = sum(float(r[f"{key}_total_error"]) <= float(r["error"]) for r in ok)
        bad = sum(float(r[f"{key}_solver_error"]) > float(r["error"]) / 4 for r in ok)
        awful = sum(float(r[f"{key}_solver_error"]) > float(r["error"]) for r in ok)
        print(f"\n{label}: {n} settings")
        print(f"  angles computed: {len(ok)}   crash: {st.count('crash')}   too large to compute: {st.count('too_large')}")
        print(f"  total error <= eps: {meets}   > eps: {len(ok) - meets}")
        print(f"  angle error > eps/4 (its budget): {bad}   > eps: {awful}")


if __name__ == "__main__":
    main()
