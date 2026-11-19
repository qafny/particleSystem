"""Check the QSVT phases of every benchmark circuit (path 8 in mlqblue/job_lcu.csv).

mlqblue/phasecheck solves, with the extracted QBlueQSVT.qsvt_phases, the two
polynomials of each job's QSVT segment, (1 - eta) cos(tau x) and
(1 - eta) sin(tau x), with tau, eta and the degree exactly as qsvt_circuit
computes them. This script runs it, evaluates the circuit the phases define,
Re <0| e^{i phi_0 Z} prod_k (W(x) e^{i phi_k Z}) |0>, on 4001 points of
[-1, 1], and compares it with the target polynomial. The phase error should be
far below the segment's error budget eta = err / (8 r).

Run from the repository root after `make build`:
  .venv/bin/python scripts/check_qsvt_phases.py
writes results/qsvt_phase_check.csv and prints a summary; exits 1 if any
polynomial fails (non-finite phases, or error above --tol).
"""

import argparse
import csv
import json
import subprocess
import sys
from pathlib import Path

import numpy as np
from numpy.polynomial import chebyshev as C

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "mlqblue/_build/default/phasecheck/phasecheck.exe"


def re_u00(ph, x):
    s = np.sqrt(np.maximum(0.0, 1 - x * x))
    a = np.exp(1j * ph[0]) * np.ones_like(x, complex)
    b = np.zeros_like(a)
    for p in ph[1:]:
        a, b = x * a + 1j * s * b, 1j * s * a + x * b
        a, b = a * np.exp(1j * p), b * np.exp(-1j * p)
    return a.real


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--jobs", default=str(ROOT / "mlqblue/job_lcu.csv"))
    ap.add_argument("--data", default=str(ROOT / "mlqblue"))
    ap.add_argument("--output", default=str(ROOT / "results/qsvt_phase_check.csv"))
    ap.add_argument("--tol", type=float, default=1e-10, help="largest acceptable phase error")
    ap.add_argument("--lbfgs", action="store_true",
                    help="also score Ian's Dong-Lin L-BFGS alone, before the Newton refinement")
    args = ap.parse_args()

    cmd = [str(EXE), args.jobs, args.data] + (["lbfgs"] if args.lbfgs else [])
    proc = subprocess.run(cmd, capture_output=True, text=True, check=True)
    xs = np.linspace(-1, 1, 4001)
    rows = []
    for line in proc.stdout.splitlines():
        r = json.loads(line.replace("nan", "NaN").replace("inf", "Infinity"))
        ph = np.array(r["phases"], float)
        f = C.chebval(xs, r["cheb"])
        err = float(np.abs(re_u00(ph, xs) - f).max()) if np.all(np.isfinite(ph)) else float("nan")
        row = dict(file_name=r["file_name"], error=r["error"], time=r["time"], segments=r["segments"],
                   tau=r["tau"], eta=r["eta"], target=r["target"], degree=len(ph) - 1,
                   phase_error=err, seconds=r["seconds"])
        if "lbfgs_phases" in r:
            lb = np.array(r["lbfgs_phases"], float)
            row["lbfgs_error"] = float(np.abs(re_u00(lb, xs) - f).max()) if np.all(np.isfinite(lb)) else float("nan")
            row["lbfgs_seconds"] = r["lbfgs_seconds"]
        rows.append(row)
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, "w", newline="") as f:
        w = csv.DictWriter(f, list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    errs = np.array([r["phase_error"] for r in rows])
    bad = [r for r in rows if not np.isfinite(r["phase_error"]) or r["phase_error"] > args.tol]
    ratio = np.array([r["phase_error"] / r["eta"] for r in rows if np.isfinite(r["phase_error"])])
    degs = [r["degree"] for r in rows]
    secs = [r["seconds"] for r in rows]
    print(f"{len(rows)} polynomials ({len(rows) // 2} QSVT settings, cos and sin), degree {min(degs)}-{max(degs)}")
    print(f"phase error: max {np.nanmax(errs):.1e}, median {np.nanmedian(errs):.1e}; "
          f"largest error / budget eta: {ratio.max():.1e}")
    print(f"failures (non-finite or > {args.tol:g}): {len(bad)}")
    if args.lbfgs:
        lb = np.array([r["lbfgs_error"] for r in rows])
        alone = int(np.sum(np.isfinite(lb) & (lb <= args.tol)))
        print(f"Ian's L-BFGS alone: within {args.tol:g} on {alone} of {len(rows)}; "
              f"median error {np.nanmedian(lb):.1e}, worst {np.nanmax(lb):.1e}, non-finite {int(np.sum(~np.isfinite(lb)))}")
    print(f"solve time: median {np.median(secs):.3f} s, max {max(secs):.2f} s, total {sum(secs):.0f} s")
    print(f"wrote {args.output}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
