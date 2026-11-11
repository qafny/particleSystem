"""PennyLane baseline for the LCU run (mlqblue/job_lcu.csv, results/lcu_results.csv).

PennyLane simulates e^{-iHt} with generalized QSP (Motlagh, Wiebe 2024) on the
qubitization walk W = Reflection . PrepSelPrep, the same algorithm as QBlue's
QSP path (9). Three counts per (program, error, time):

  pl_est         pennylane.estimator.GQSPTimeEvolution(Qubitization(
                 QROMStatePreparation, SelectPauli)): PennyLane's resource model,
                 with unary-iteration Select (Babbush et al. 2018) and QROM state
                 preparation. PennyLane picks the degree (GQSPTimeEvolution.
                 poly_approx: smallest N >= lambda t with |J_{N+1}(lambda t)| <=
                 eps/2) and runs one segment; the identity term is dropped (a
                 global phase), so lambda is the one-norm without it.
  pl_est_qbpoly  The same resource model at QBlue's segments and degree: r
                 segments of GQSP(W, d+ = K, d- = K), with QBlue's terms
                 (identity included), lambda, r and K.
  pl_circuit     The real circuit, built from PennyLane's templates and
                 decomposed by PennyLane into CNOT and single-qubit gates:
                 r segments of GQSP(Qubitization(H), 2K) followed by K inverse
                 walks, exactly QBlue's QSP circuit structure, terms, r and K.
                 Only programs with at most --max-terms terms (decomposition is
                 slow). Counted per piece: GQSP(d) = base + d * layer from the
                 decompositions at d = 1 and d = 2, plus the inverse walk.

Rotations are counted as single gates (RX/RY/RZ/U3), not synthesized into T,
matching how QBlue counts. Toffolis are decomposed. No optimization passes are
run on PennyLane's output, so compare it with QBlue's counts before VOQC
(*_bfopt) as well as after.

--check builds the full circuit for a few tiny programs, compares it with
exp(-iHt), and checks the piece count against the full decomposition.

Run with a Python that has pennylane, kept out of the pipeline venv:
  ~/pl-venv/bin/python scripts/pennylane_lcu.py --workers 8
"""

import argparse
import csv
import math
import os
import sys
import time
import traceback
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import numpy as np
from scipy.special import jv

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "mlqblue"
FIELDS = ["file_name", "error", "time", "method", "nqubit", "program_size", "one_norm", "segments",
          "poly_degree", "qubits", "single_qubit_gates", "multi_qubit_gates", "t_gates", "seconds",
          "status", "message"]
EST_GATES = {"CNOT", "X", "Y", "Z", "S", "Hadamard", "T", "RZ", "RY", "RX"}
CIRC_GATES = {"CNOT", "RX", "RY", "RZ", "Hadamard", "PauliX", "PauliY", "PauliZ", "S", "Adjoint(S)",
              "T", "Adjoint(T)", "GlobalPhase", "PhaseShift"}
QSP_TAU_MAX = 10.0   # QBlueQubitization.qsp_tau_max


def read_program(path):
    terms = []
    for line in open(path):
        if "*" not in line:
            continue
        c, p = line.split("*")
        c = float(c.replace(" ", ""))
        if c != 0:
            terms.append((c, p.strip()))
    return terms


# ---- QBlue's QSP parameters (QBlueQubitization.qsp_circuit) -----------------

def find_k(tau, eps):
    """smallest K with sum_{k > K} 2 |J_k(tau)| < eps (QBlueQuantumWalk.findK_qwalk)"""
    tau, eps = abs(tau), max(eps, 1e-18)
    top = int(tau * 2 + 40 + math.log(1 / eps) * 2)
    tail, best = 0.0, top
    for k in range(top, 0, -1):
        tail += 2 * abs(jv(k, tau))
        if tail < eps:
            best = k - 1
    return best


def qblue_qsp_params(terms, t, eps):
    lam = sum(abs(c) for c, _ in terms)
    r = max(1, math.ceil(lam * t / QSP_TAU_MAX))
    tau = lam * t / r
    delta = eps / (4 * r)
    return lam, r, tau, delta, max(1, find_k(tau, delta))


# ---- resource estimator -------------------------------------------------------

def est_walk(terms, n, drop_identity):
    import pennylane.estimator as qre
    if drop_identity:
        terms = [(c, p) for c, p in terms if set(p) != {"I"}]
    words = Counter("".join(sorted(ch for ch in p if ch != "I")) for _, p in terms)
    words.pop("", None)
    lam = sum(abs(c) for c, _ in terms)
    a = max(1, math.ceil(math.log2(max(2, len(terms)))))
    ham = qre.PauliHamiltonian(num_qubits=n, pauli_terms=dict(words), one_norm=lam)
    return qre.Qubitization(qre.QROMStatePreparation(a, positive_and_real=True), qre.SelectPauli(ham)), lam


def est_counts(res):
    g = res.gate_counts
    multi = g.get("CNOT", 0)
    single = sum(v for k, v in g.items() if k != "CNOT")
    return res.total_wires, single, multi, g.get("T", 0)


def run_estimator(terms, n, settings):
    import pennylane.estimator as qre
    rows = []
    walk, lam = est_walk(terms, n, drop_identity=True)
    walk_qb, lam_qb = est_walk(terms, n, drop_identity=False)
    for eps, t in settings:
        t0 = time.time()
        deg = qre.GQSPTimeEvolution.poly_approx(t, lam, eps)
        res = qre.estimate(qre.GQSPTimeEvolution(walk, time=t, one_norm=lam, poly_approx_precision=eps),
                           gate_set=EST_GATES)
        rows.append(dict(error=eps, time=t, method="pl_est", one_norm=lam, segments=1, poly_degree=2 * deg,
                         **dict(zip(["qubits", "single_qubit_gates", "multi_qubit_gates", "t_gates"], est_counts(res))),
                         seconds=time.time() - t0))
        t0 = time.time()
        _, r, _, _, K = qblue_qsp_params(terms, t, eps)
        seg = qre.estimate(qre.GQSP(walk_qb, d_plus=K, d_minus=K), gate_set=EST_GATES)
        q, s, m, tg = est_counts(seg)
        rows.append(dict(error=eps, time=t, method="pl_est_qbpoly", one_norm=lam_qb, segments=r, poly_degree=2 * K,
                         qubits=q, single_qubit_gates=r * s, multi_qubit_gates=r * m, t_gates=r * tg,
                         seconds=time.time() - t0))
    return rows


# ---- real circuits ------------------------------------------------------------

def pl_hamiltonian(terms, n):
    import pennylane as qml
    ops = [qml.pauli.PauliWord({i: ch for i, ch in enumerate(p) if ch != "I"}).operation(wire_order=range(n))
           if set(p) != {"I"} else qml.Identity(0) for _, p in terms]
    return qml.Hamiltonian([c for c, _ in terms], ops)


def layout(terms, n):
    a = max(1, math.ceil(math.log2(max(2, len(terms)))))
    return list(range(n, n + a)), n + a


def circ_count(ops):
    import pennylane as qml
    [tape], _ = qml.transforms.decompose(qml.tape.QuantumScript(ops), gate_set=CIRC_GATES)
    c = Counter(o.name for o in tape.operations)
    c.pop("GlobalPhase", None)
    multi = c.get("CNOT", 0)
    return sum(c.values()) - multi, multi


def segment_ops(H, idx, sig, angles, K):
    import pennylane as qml
    ops = [qml.GQSP(qml.Qubitization(H, control=idx), angles, control=sig)]
    ops += [qml.adjoint(qml.Qubitization(H, control=idx)) for _ in range(K)]
    return ops


def circuit_pieces(terms, n):
    """(single, multi) of GQSP at d = 1 and 2 and of one inverse walk"""
    import pennylane as qml
    qml.decomposition.enable_graph()
    H = pl_hamiltonian(terms, n)
    idx, sig = layout(terms, n)
    g = [circ_count([qml.GQSP(qml.Qubitization(H, control=idx), np.full((3, d + 1), 0.3), control=sig)])
         for d in (1, 2)]
    inv = circ_count([qml.adjoint(qml.Qubitization(H, control=idx))])
    return g, inv, n + len(idx) + 1


def run_circuit(terms, n, settings):
    t0 = time.time()
    (g1, g2), inv, nq = circuit_pieces(terms, n)
    piece_time = time.time() - t0
    rows = []
    for eps, t in settings:
        lam, r, _, _, K = qblue_qsp_params(terms, t, eps)
        d = 2 * K
        seg = [g1[i] + (d - 1) * (g2[i] - g1[i]) + K * inv[i] for i in (0, 1)]
        rows.append(dict(error=eps, time=t, method="pl_circuit", one_norm=lam, segments=r, poly_degree=d,
                         qubits=nq, single_qubit_gates=r * seg[0], multi_qubit_gates=r * seg[1], t_gates="",
                         seconds=piece_time))
    return rows


def check(path):
    """full circuit vs exp(-iHt) and vs the piece count, for one tiny program"""
    import pennylane as qml
    import scipy.linalg as sl
    qml.decomposition.enable_graph()
    terms = read_program(path)
    n = len(terms[0][1])
    t, eps = 1.0, 0.01
    lam, r, tau, delta, K = qblue_qsp_params(terms, t, eps)
    # e^{-i tau x} = sum_n (-i)^|n| J_|n|(tau) T_|n|(x), as z^{-K} P(z) on the walk
    poly = np.array([(1 - delta) * (-1j) ** abs(k - K) * jv(abs(k - K), tau) for k in range(2 * K + 1)])
    angles = qml.poly_to_angles(poly, "GQSP")
    H = pl_hamiltonian(terms, n)
    idx, sig = layout(terms, n)
    ops = [o for _ in range(r) for o in segment_ops(H, idx, sig, angles, K)]
    U = qml.matrix(lambda: [qml.apply(o) for o in ops], wire_order=[sig] + idx + list(range(n)))()
    blk = U[: 2 ** n, : 2 ** n]
    err = np.linalg.norm(blk - sl.expm(-1j * qml.matrix(H, wire_order=range(n)) * t), 2)
    full = circ_count(ops)
    [row] = run_circuit(terms, n, [(eps, t)])
    pieces = (row["single_qubit_gates"], row["multi_qubit_gates"])
    print(f"{Path(path).name}: n={n} L={len(terms)} r={r} K={K} error {err:.1e} (bound {eps}) "
          f"full={full} pieces={pieces} {'MATCH' if tuple(full) == pieces else 'MISMATCH'}", flush=True)
    return err < eps and tuple(full) == pieces


def job(file_name, settings, circuit, max_terms):
    path = DATA / file_name
    terms = read_program(path)
    n = len(terms[0][1])
    base = dict(file_name=file_name, nqubit=n, program_size=len(terms), status="ok", message="")
    out = []
    for runner, on in ((run_estimator, True), (run_circuit, circuit and len(terms) <= max_terms)):
        if not on:
            continue
        try:
            out += [{**base, **row} for row in runner(terms, n, settings)]
        except Exception as e:  # keep going; the row records why
            out += [{**base, "error": eps, "time": t, "method": runner.__name__, "status": "error",
                     "message": f"{type(e).__name__}: {e}"[:300]} for eps, t in settings]
            traceback.print_exc()
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--input", default=str(DATA / "job_lcu.csv"))
    ap.add_argument("--output", default=str(ROOT / "results/pennylane_lcu.csv"))
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--no-circuit", action="store_true", help="estimator only")
    ap.add_argument("--max-terms", type=int, default=250, help="largest program to decompose")
    ap.add_argument("--check", nargs="*", metavar="FILE", help="check tiny programs and exit")
    args = ap.parse_args()

    if args.check is not None:
        ok = all(check(f) for f in args.check)
        return 0 if ok else 1

    jobs = {}
    with open(args.input) as f:
        for row in csv.DictReader(f):
            jobs.setdefault(row["file_name"], set()).add((float(row["error"]), float(row["time"])))
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    rows = []
    with ProcessPoolExecutor(args.workers) as pool:
        futs = {pool.submit(job, f, sorted(s), not args.no_circuit, args.max_terms): f for f, s in jobs.items()}
        for i, fut in enumerate(as_completed(futs), 1):
            rows += fut.result()
            print(f"[{i}/{len(futs)}] {futs[fut]}", flush=True)
            with open(args.output, "w", newline="") as f:
                w = csv.DictWriter(f, FIELDS)
                w.writeheader()
                w.writerows(sorted(rows, key=lambda r: (r["file_name"], r["method"], r["error"], r["time"])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
