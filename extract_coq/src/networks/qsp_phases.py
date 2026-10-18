"""Phase solvers for the QSP-based LCU methods (QBlueQSVT.v, QBlueQubitization.v).

qsvt_phases(cheb, parity)
    Symmetric QSP phases (Wx convention) with Re <0|U_Phi(x)|0> = f(x), where f
    has the given Chebyshev coefficients and parity; Newton iteration on the
    reduced phases (Dong, Lin, Ni, Wang, "Efficient phase-factor evaluation in
    quantum signal processing", 2021).

gqsp_complement(re, im)
    The complementary polynomial for generalized QSP; the angles themselves are
    computed in Coq by layer stripping (QBlueQubitization.gqsp_angles).

gqsp_angles(p)
    Reference implementation of the generalized QSP angles, not used by the
    compiler (Motlagh, Wiebe, "Generalized quantum signal processing", 2024),
    for P(z) = sum_k p_k z^k with |P| < 1 on |z| = 1. The
    complementary polynomial Q (|P|^2 + |Q|^2 = 1) is the Fejer-Riesz factor
    from the roots inside the unit circle, and the angles come from layer
    stripping. Both run in multiprecision: when |P| is close to 1, Q is small
    and double precision loses its phase.
"""
import numpy as np
from numpy.polynomial import chebyshev as cheb


def _full_phases(red, d):
    return np.concatenate([red[::-1], red]) if d % 2 else np.concatenate([red[:0:-1], red])


def _qsp_poly(phis, x):
    s = np.sqrt(1 - x ** 2)
    a = np.exp(1j * phis[0]) * np.ones_like(x, complex)
    b = np.zeros_like(x, complex)
    for p in phis[1:]:
        a, b = a * x + b * 1j * s, a * 1j * s + b * x
        a, b = a * np.exp(1j * p), b * np.exp(-1j * p)
    return a


def qsvt_phases(coeffs, parity, tol=1e-12, maxit=100):
    coeffs = np.asarray(coeffs, float)
    d = len(coeffs) - 1
    if d % 2 != parity:
        d += 1
        coeffs = np.append(coeffs, 0.0)
    dt = (d + 2) // 2
    xs = np.cos((2 * np.arange(1, dt + 1) - 1) * np.pi / (4 * dt))
    target = cheb.chebval(xs, coeffs)
    red = np.zeros(dt)
    red[-1] = np.pi / 4

    def F(r):
        return _qsp_poly(_full_phases(r, d), xs).real

    for _ in range(maxit):
        res = F(red) - target
        if np.abs(res).max() < tol:
            return _full_phases(red, d).tolist()
        h = 1e-7
        J = np.empty((dt, dt))
        for k in range(dt):
            e = np.zeros(dt)
            e[k] = h
            J[:, k] = (F(red + e) - F(red - e)) / (2 * h)
        red = red - np.linalg.solve(J, res)
    raise RuntimeError(f"QSP Newton iteration did not converge (residual {np.abs(res).max():.2e})")


def gqsp_angles(re, im, dps=60):
    import mpmath as mp
    mp.mp.dps = dps
    p = [mp.mpc(a, b) for a, b in zip(re, im)]
    d = len(p) - 1
    g = [mp.mpc(0)] * (2 * d + 1)                  # 1 - P(z) conj(P)(1/z), powers -d..d
    for i in range(d + 1):
        for j in range(d + 1):
            g[d + i - j] -= p[i] * mp.conj(p[j])
    g[d] += 1
    roots = mp.polyroots(g[::-1], maxsteps=400, extraprec=4 * dps)
    q = [mp.mpc(1)]
    for r in sorted(roots, key=abs)[:d]:
        q = [(q[k - 1] if k > 0 else 0) - r * (q[k] if k < len(q) else 0) for k in range(len(q) + 1)]
    scale = mp.sqrt(mp.re(sum(g))) / abs(sum(q))   # match |Q(1)|^2 = g(1)
    q = [c * scale for c in q]
    thetas, phis = [mp.mpf(0)] * (d + 1), [mp.mpf(0)] * (d + 1)
    P, Q = p, q
    for j in range(d, 0, -1):
        pj, qj = P[j], Q[j]
        th = mp.atan2(abs(qj), abs(pj))
        ph = mp.arg(pj) - mp.arg(qj) if abs(qj) > 0 and abs(pj) > 0 else mp.mpf(0)
        thetas[j], phis[j] = th, ph
        c, s, e = mp.cos(th), mp.sin(th), mp.exp(-1j * ph)
        top = [e * c * a + s * b for a, b in zip(P, Q)]
        bot = [e * s * a - c * b for a, b in zip(P, Q)]
        P, Q = top[1:j + 1], bot[:j]
    thetas[0] = mp.atan2(abs(Q[0]), abs(P[0]))
    lam = mp.arg(Q[0])
    phis[0] = mp.arg(P[0]) - lam
    return [float(x) for x in thetas] + [float(x) for x in phis] + [float(lam)]


def gqsp_complement(re, im, dps=60):
    """Q (real parts ++ imaginary parts) with |P|^2 + |Q|^2 = 1 on |z| = 1:
    the Fejer-Riesz factor of 1 - |P|^2 from its roots inside the unit circle,
    in multiprecision. QBlueQubitization.gqsp_angles strips the layers in Coq."""
    import mpmath as mp
    mp.mp.dps = dps
    p = [mp.mpc(a, b) for a, b in zip(re, im)]
    d = len(p) - 1
    g = [mp.mpc(0)] * (2 * d + 1)
    for i in range(d + 1):
        for j in range(d + 1):
            g[d + i - j] -= p[i] * mp.conj(p[j])
    g[d] += 1
    roots = mp.polyroots(g[::-1], maxsteps=400, extraprec=4 * dps)
    q = [mp.mpc(1)]
    for r in sorted(roots, key=abs)[:d]:
        q = [(q[k - 1] if k > 0 else 0) - r * (q[k] if k < len(q) else 0) for k in range(len(q) + 1)]
    scale = mp.sqrt(mp.re(sum(g))) / abs(sum(q))
    q = [c * scale for c in q]
    return [float(mp.re(c)) for c in q] + [float(mp.im(c)) for c in q]
