"""Check the extracted LCU circuits (paths 8, 9, 30, 31) against exact evolution.

For random small Hamiltonians, mlqblue/lcucheck dumps the circuit each method
builds; a statevector simulation computes <0_anc| C |0_anc> on the system
qubits and compares it with exp(-iHt) up to a global phase (the error must be
below the requested bound). `--counts` also checks that the resource pieces the
compiler counts add up to the full circuit. Run from the repository root after
`make build`, with the virtual environment that runs the pipeline.
"""

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "mlqblue/_build/default/lcucheck/lcucheck.exe"
PAULI = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]], complex),
         "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1, -1]).astype(complex)}
H1 = np.array([[1, 1], [1, -1]]) / np.sqrt(2)


def u3(th, ph, lam):
    return np.array([[np.cos(th / 2), -np.exp(1j * lam) * np.sin(th / 2)],
                     [np.exp(1j * ph) * np.sin(th / 2), np.exp(1j * (ph + lam)) * np.cos(th / 2)]])


def apply1(psi, m, q, n):
    ax = n - 1 - q
    psi = np.moveaxis(np.tensordot(m, np.moveaxis(psi.reshape([2] * n), ax, 0), axes=1), 0, ax)
    return psi.reshape(-1)


def run(circ, psi, n):
    """qubit q is bit q of the basis index"""
    idx = np.arange(len(psi))
    for g in circ:
        k = g[0]
        if k == "x":
            psi = psi[idx ^ (1 << g[1])]
        elif k == "h":
            psi = apply1(psi, H1, g[1], n)
        elif k == "u1":
            psi = psi * np.where((idx >> g[2]) & 1, np.exp(1j * g[1]), 1)
        elif k == "u3":
            psi = apply1(psi, u3(*g[1:4]), g[4], n)
        elif k == "cx":
            psi = np.where((idx >> g[1]) & 1, psi[idx ^ (1 << g[2])], psi)
        else:                                            # ccx
            on = ((idx >> g[1]) & 1) & ((idx >> g[2]) & 1)
            psi = np.where(on, psi[idx ^ (1 << g[3])], psi)
    return psi


def load(path):
    circ, nq = [], 0
    for line in open(path):
        p = line.split()
        k, nums = p[0], p[1:]
        if k in ("u1", "u3"):
            g = (k, *map(float, nums[:-1]), int(nums[-1]))
        else:
            g = (k, *map(int, nums))
        circ.append(g)
        nq = max(nq, max(x for x in g[1:] if isinstance(x, int)) + 1)
    return circ, nq


def hamiltonian(terms, n):
    """terms: (coef, label) with character i acting on qubit i"""
    m = np.zeros((2 ** n, 2 ** n), complex)
    for c, label in terms:
        op = np.array([[1.0 + 0j]])
        for ch in reversed(label):
            op = np.kron(op, PAULI[ch])
        m += c * op
    return m


def write_ham(terms, path):
    path.write_text("".join(f"{'+' if c >= 0 else '-'} {abs(c):.15f} * {p}\n" for c, p in terms))


def check(terms, method, eps, t, workdir):
    n = len(terms[0][1])
    ham = workdir / "h.txt"
    write_ham(terms, ham)
    out = workdir / "c.txt"
    subprocess.run([str(EXE), str(ham), method, str(eps), str(t), str(out)],
                   check=True, capture_output=True, text=True)
    circ, nq = load(out)
    nq = max(nq, n)
    d = 2 ** n
    block = np.zeros((d, d), complex)
    for j in range(d):
        psi = np.zeros(2 ** nq, complex)
        psi[j] = 1
        block[:, j] = run(circ, psi, nq)[:d]
    w, v = np.linalg.eigh(hamiltonian(terms, n))
    want = v @ np.diag(np.exp(-1j * w * t)) @ v.conj().T
    tr = np.trace(want.conj().T @ block)
    phase = tr / abs(tr) if abs(tr) > 1e-12 else 1
    return np.linalg.norm(block - phase * want, 2), nq, len(circ)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("methods", nargs="*", default=["taylor", "qwalk", "qsp", "qsvt"])
    parser.add_argument("--counts", action="store_true", help="also check pieces against the full circuit")
    parser.add_argument("--seed", type=int, default=7)
    args = parser.parse_args()
    if not EXE.exists():
        sys.exit(f"{EXE} not found: run `make build` (it builds mlqblue/lcucheck) first")
    os.environ.setdefault("QBLUE_API_PY", str(ROOT / "extract_coq/src/networks/api.py"))
    os.environ["PATH"] = str(Path(sys.executable).parent) + os.pathsep + os.environ.get("PATH", "")
    rng = np.random.default_rng(args.seed)
    # (qubits, terms, t, eps); the last QSVT/QSP cases need several segments
    cases = [(1, 2, 0.5, 1e-2), (2, 2, 0.785, 1e-2), (2, 3, 2.0, 1e-2), (1, 2, 40.0, 1e-2)]
    failed = 0
    with tempfile.TemporaryDirectory() as d:
        workdir = Path(d)
        for method in args.methods:
            for n, L, t, eps in cases:
                if method == "taylor" and (L > 2 or t > 1):
                    continue        # Taylor's registers grow too large to simulate
                if method in ("qwalk",) and t > 10:
                    continue
                terms = [(rng.normal(), "".join(rng.choice(list("IXYZ"), n))) for _ in range(L)]
                err, nq, ng = check(terms, method, eps, t, workdir)
                ok = err < eps
                failed += not ok
                print(f"{method:6s} n={n} L={L} t={t:<5} eps={eps}: {nq:2d} qubits, {ng:6d} gates, "
                      f"error {err:.1e} {'OK' if ok else 'FAIL'}", flush=True)
            if args.counts:
                write_ham([(0.7, "ZIX"), (-0.4, "XYI"), (0.25, "IZZ")], workdir / "h3.txt")
                res = subprocess.run([str(EXE), str(workdir / "h3.txt"), method, "0.01", "1.3",
                                      str(workdir / "c3.txt"), "counts"], check=True,
                                     capture_output=True, text=True).stdout.strip().splitlines()[-1]
                failed += "MISMATCH" in res
                print("  " + res, flush=True)
    return int(failed > 0)


if __name__ == "__main__":
    raise SystemExit(main())
