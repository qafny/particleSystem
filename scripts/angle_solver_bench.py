"""GQSP angle solvers on the Jacobi-Anger polynomial for e^{-i tau cos theta}.

For each tau, the degree is PennyLane's own (GQSPTimeEvolution.poly_approx at
error 1e-3, degree 2N), and the polynomial z^N sum_{|k|<=N} (-i)^|k| J_|k|(tau) z^k
is rescaled so |P| <= 1 - 1e-3 on the unit circle (unscaled, PennyLane's degree
often leaves |P| > 1, and poly_to_angles then crashes with a shape error).

  pl    qml.poly_to_angles(P, "GQSP"); the error is max |P(z) - <0|GQSP|0>|
        over the unit circle, evaluating the circuit its angles define
        (GQSP.compute_decomposition with U = z).
  ours  qsp_phases.gqsp_complement, the complementary polynomial QBlue's
        layer stripping uses (60-digit mpmath roots); the error is
        max ||P|^2 + |Q|^2 - 1|.

One JSON line per run. Run each case in its own process with a timeout:
  for tau in 25 50 100 200 400 800 1600; do
    timeout 1200 ~/pl-venv/bin/python scripts/angle_solver_bench.py pl $tau; done
"""

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.special import jv

ROOT = Path(__file__).resolve().parents[1]
EPS = 1e-3


def u3(th, ph, la):
    c, s = np.cos(th / 2), np.sin(th / 2)
    return np.array([[c, -np.exp(1j * la) * s], [np.exp(1j * ph) * s, np.exp(1j * (ph + la)) * c]])


X, Z = np.array([[0, 1], [1, 0]]), np.diag([1, -1])


def gqsp_value(angles, z):
    th, ph, la = angles
    M = Z @ X @ u3(2 * th[0], ph[0], la[0]) @ X
    C = np.diag([z, 1])
    for t_, p_, l_ in zip(th[1:], ph[1:], la[1:]):
        M = Z @ X @ u3(2 * t_, p_, l_) @ X @ C @ M
    return M[0, 0]


def target(tau):
    import pennylane.estimator as qre
    N = qre.GQSPTimeEvolution.poly_approx(1.0, tau, EPS)
    poly = np.array([(-1j) ** abs(k - N) * jv(abs(k - N), tau) for k in range(2 * N + 1)])
    zs = np.exp(1j * np.linspace(0, 2 * np.pi, 16 * len(poly) + 64, endpoint=False))
    return poly * (1 - EPS) / np.abs(np.polynomial.polynomial.polyval(zs, poly)).max()


def main():
    who, tau = sys.argv[1], float(sys.argv[2])
    poly = target(tau)
    d = len(poly) - 1
    zs = np.exp(1j * np.linspace(0, 2 * np.pi, min(4 * d + 7, 1201), endpoint=False))
    t0 = time.time()
    out = dict(who=who, tau=tau, degree=d)
    try:
        if who == "pl":
            import pennylane as qml
            ang = np.asarray(qml.poly_to_angles(poly, "GQSP"))
            out["seconds"] = round(time.time() - t0, 2)
            got = np.array([gqsp_value(ang, z) for z in zs])
            out["error"] = float(np.abs(got - np.polynomial.polynomial.polyval(zs, poly)).max())
        else:
            sys.path.insert(0, str(ROOT / "extract_coq/src/networks"))
            import qsp_phases
            q = qsp_phases.gqsp_complement(list(poly.real), list(poly.imag))
            out["seconds"] = round(time.time() - t0, 2)
            q = np.array(q[: d + 1]) + 1j * np.array(q[d + 1:])
            pv, qv = (np.polynomial.polynomial.polyval(zs, c) for c in (poly, q))
            out["error"] = float(np.abs(np.abs(pv) ** 2 + np.abs(qv) ** 2 - 1).max())
    except Exception as e:
        out.update(seconds=round(time.time() - t0, 2), failed=f"{type(e).__name__}: {str(e)[:120]}")
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
