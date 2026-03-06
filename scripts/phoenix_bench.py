#!/usr/bin/env python3
"""
Benchmark Phoenix (thirdparty/phoenix) on the QBlue benchmark datasets.

This script parses MarQSim/Genesis Hamiltonian text files into Pauli strings +
coefficients, compiles them with Phoenix, and writes a CSV with wall-clock time
and gate/qubit counts.

Notes:
- Phoenix uses Qiskit. You likely want a separate venv that can install qiskit
  (Python 3.12 is a safer default than 3.13 as of early 2026).
- Genesis inputs are parsed directly; constant (all-'I') terms are dropped by
  default since they only contribute a global phase.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PHOENIX_DIR = ROOT / "thirdparty" / "phoenix"

_MARQSIM_TERM_RE = re.compile(
    r"^\s*([+-])\s+([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)\s*\*\s*([IXYZ]+)\s*$"
)
_GENESIS_TERM_RE = re.compile(r"^\s*([IXYZ]+)\s+\(([^)]+)\)\s*$")


def detect_format(path: Path) -> str:
    # Return "marqsim" | "genesis" | "unknown"
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for _ in range(50):
            line = f.readline()
            if not line:
                break
            s = line.strip()
            if not s:
                continue
            if _MARQSIM_TERM_RE.match(s):
                return "marqsim"
            if _GENESIS_TERM_RE.match(s):
                return "genesis"
    return "unknown"


def iter_input_files(dataset: str) -> list[Path]:
    base = ROOT / "QBlue_Benchmark_Datasets"
    if dataset == "marqsim":
        files = list((base / "MarQSim_dataset").glob("*.txt"))
        return sorted(files, key=lambda p: (p.stat().st_size, str(p)))
    if dataset == "genesis":
        files = list((base / "Genesis_dataset").rglob("*.txt"))
        return sorted(files, key=lambda p: (p.stat().st_size, str(p)))
    if dataset == "all":
        mar = list((base / "MarQSim_dataset").glob("*.txt"))
        mar = sorted(mar, key=lambda p: (p.stat().st_size, str(p)))
        gen = list((base / "Genesis_dataset").rglob("*.txt"))
        gen = sorted(gen, key=lambda p: (p.stat().st_size, str(p)))
        return mar + gen
    raise ValueError(f"unknown dataset: {dataset}")


@dataclass(frozen=True)
class ParsedHamiltonian:
    paulis: list[str]
    coeffs: list[complex]

    @property
    def n_terms(self) -> int:
        return len(self.paulis)

    @property
    def n_qubits(self) -> int:
        return len(self.paulis[0]) if self.paulis else 0


def _is_identity_term(label: str) -> bool:
    return all(ch == "I" for ch in label)


def parse_hamiltonian_file(
    path: Path,
    *,
    keep_identity: bool,
    reverse_labels: bool,
) -> ParsedHamiltonian:
    fmt = detect_format(path)
    text = path.read_text(encoding="utf-8", errors="replace")

    paulis: list[str] = []
    coeffs: list[complex] = []

    if fmt == "marqsim":
        for raw in text.splitlines():
            line = raw.strip()
            if not line:
                continue
            m = _MARQSIM_TERM_RE.match(line)
            if not m:
                continue
            sign_s, coeff_s, label = m.groups()
            coeff = float(coeff_s)
            if sign_s == "-":
                coeff = -coeff
            if reverse_labels:
                label = label[::-1]
            if not keep_identity and _is_identity_term(label):
                continue
            if coeff == 0.0:
                continue
            paulis.append(label)
            coeffs.append(complex(coeff))
        return ParsedHamiltonian(paulis=paulis, coeffs=coeffs)

    if fmt == "genesis":
        for raw in text.splitlines():
            line = raw.strip()
            if not line:
                continue
            m = _GENESIS_TERM_RE.match(line)
            if not m:
                continue
            label, coeff_s = m.groups()
            try:
                coeff = complex(coeff_s.replace(" ", "").strip())
            except ValueError:
                continue
            if reverse_labels:
                label = label[::-1]
            if not keep_identity and _is_identity_term(label):
                continue
            if coeff == 0:
                continue
            paulis.append(label)
            coeffs.append(coeff)
        return ParsedHamiltonian(paulis=paulis, coeffs=coeffs)

    raise ValueError(f"Unrecognized dataset format for {path} (expected MarQSim or Genesis)")


def _ensure_joblib_or_stub() -> None:
    """
    Phoenix's `phoenix/__init__.py` imports `phoenix.compiler`, which imports
    `joblib` at module import time. For our benchmark script we compile
    sequentially and do not require joblib, so we provide a tiny stub if the
    dependency is missing.
    """

    try:
        import joblib  # noqa: F401
        return
    except ModuleNotFoundError:
        pass

    import types

    def delayed(func):
        def _wrap(*args, **kwargs):
            return lambda: func(*args, **kwargs)

        return _wrap

    class Parallel:
        def __init__(self, *args, **kwargs):
            pass

        def __call__(self, tasks):
            out = []
            for t in tasks:
                if callable(t):
                    out.append(t())
                else:
                    out.append(t)
            return out

    stub = types.ModuleType("joblib")
    stub.delayed = delayed
    stub.Parallel = Parallel
    sys.modules["joblib"] = stub


def _require_phoenix_and_qiskit() -> None:
    if not PHOENIX_DIR.exists():
        raise FileNotFoundError(
            f"Missing {PHOENIX_DIR}.\n"
            "Clone Phoenix into thirdparty/ first, e.g.\n"
            "  git clone https://github.com/iqubit-org/phoenix thirdparty/phoenix"
        )

    # Make sure we import the vendored Phoenix.
    sys.path.insert(0, str(PHOENIX_DIR))

    try:
        import qiskit  # noqa: F401
    except ModuleNotFoundError as e:
        raise ModuleNotFoundError(
            "Missing Python dependency: qiskit.\n"
            "Suggestion: create a Python 3.12 venv and install deps needed by Phoenix."
        ) from e

    _ensure_joblib_or_stub()
    try:
        import phoenix  # noqa: F401
    except ModuleNotFoundError as e:
        raise ModuleNotFoundError(
            "Could not import `phoenix` from thirdparty/phoenix.\n"
            f"Import failed due to missing dependency: {e.name!r}"
        ) from e


def _optimize_phoenix_circuit_by_qiskit(qc):
    # Inline version of phoenix.compiler.optimize_phoenix_circuit_by_qiskit
    # (avoids importing phoenix.compiler which depends on joblib).
    from itertools import product

    from qiskit.transpiler import PassManager, passes

    from phoenix.basics import CNOTEquivCliffordGate

    inverse_list = [CNOTEquivCliffordGate(p0, p1) for p0, p1 in product(["x", "y", "z"], repeat=2)]

    pm = PassManager()
    pm.append(passes.InverseCancellation(inverse_list))
    pm.append(passes.CommutativeInverseCancellation(matrix_based=True))
    pm.append(passes.Optimize1qGatesDecomposition())
    pm.append(passes.CommutativeCancellation())
    return pm.run(qc)


def phoenix_compile_to_circuit(
    ph: ParsedHamiltonian,
    *,
    time_t: float,
    order_method: str,
    qiskit_opt: bool,
):
    import numpy as np

    from phoenix.hamiltonian import Hamiltonian
    from phoenix.primitive.ordering import order_circuits
    from phoenix.primitive.simplification import simplify_hamiltonian
    from phoenix.primitive.utils import constr_circuit_from_simp_steps

    if not ph.paulis:
        raise ValueError("No Hamiltonian terms parsed")

    n = len(ph.paulis[0])
    if any(len(p) != n for p in ph.paulis):
        raise ValueError("Inconsistent Pauli string lengths in input")

    coeffs = np.asarray(ph.coeffs, dtype=np.complex128) * float(time_t)
    ham = Hamiltonian(ph.paulis, coeffs)

    # Compile sequentially (avoid multiprocessing/tooling issues in benchmark scripts).
    sub_hams = ham.group_same_weights()
    circuits = []
    for sub in sub_hams:
        sub_simplified, simp_steps = simplify_hamiltonian(sub)
        circuits.append(constr_circuit_from_simp_steps(sub_simplified, simp_steps))

    qc = order_circuits(circuits, method=order_method)
    if qiskit_opt:
        qc = _optimize_phoenix_circuit_by_qiskit(qc)
    return qc


def _count_two_qubit_gates(qc) -> int:
    count = 0
    for inst in qc.data:
        op = inst.operation
        if getattr(op, "num_qubits", 0) >= 2:
            count += 1
    return count


def _ibm_basis_gate_counts(qc, *, optimization_level: int):
    # Transpile to QBlue's (legacy) IBM gate basis and count ops so results are
    # more directly comparable to qblue_bench.py.
    from qiskit import transpile

    qc_ibm = transpile(qc, basis_gates=["u1", "u2", "u3", "cx"], optimization_level=optimization_level)
    ops = {str(k).upper(): int(v) for k, v in qc_ibm.count_ops().items()}
    return qc_ibm, ops


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["marqsim", "genesis", "all"], default="marqsim")
    ap.add_argument("--inputs", nargs="+", type=Path, default=None, help="Explicit list of input files.")
    ap.add_argument("--out", type=Path, default=Path("phoenix_results.csv"))
    ap.add_argument("--ts", nargs="+", type=float, default=[0.1], help="Evolution time(s) to benchmark.")
    ap.add_argument(
        "--order-method",
        choices=["trivial", "greedy", "greedy_multistart", "tsp", "tsp_2opt", "mcts"],
        default="trivial",
        help="Phoenix block ordering method.",
    )
    ap.add_argument("--no-qiskit-opt", action="store_true", help="Disable the final Qiskit optimization passes.")
    ap.add_argument(
        "--no-ibm-counts",
        action="store_true",
        help="Skip transpiling to the IBM (u1/u2/u3/cx) basis for QBlue-comparable counts.",
    )
    ap.add_argument("--reverse-labels", action="store_true", help="Reverse Pauli strings before giving them to Qiskit.")
    ap.add_argument(
        "--keep-identity",
        action="store_true",
        help="Keep all-'I' terms (normally dropped as they only contribute global phase).",
    )
    ap.add_argument("--limit", type=int, default=0, help="Limit number of input files (0 = no limit).")
    ap.add_argument(
        "--max-terms",
        type=int,
        default=0,
        help="Skip Hamiltonians with more than this many terms (0 = no limit).",
    )
    args = ap.parse_args()

    try:
        _require_phoenix_and_qiskit()
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    input_files = [p.resolve() for p in args.inputs] if args.inputs else iter_input_files(args.dataset)
    if args.limit and args.limit > 0:
        input_files = input_files[: args.limit]

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="", encoding="utf-8") as csvf:
        w = csv.DictWriter(
            csvf,
            fieldnames=[
                "dataset",
                "format",
                "input_path",
                "input_name",
                "t",
                "order_method",
                "qiskit_opt",
                "reverse_labels",
                "n_terms",
                "n_qubits",
                "qubits",
                "ok",
                "wall_s",
                "depth",
                "gates_total",
                "cx",
                "twoq_total",
                "ops_json",
                "ibm_depth",
                "gates_opt_total",
                "gates_opt_U1",
                "gates_opt_U2",
                "gates_opt_U3",
                "gates_opt_CX",
                "gates_opt_json",
                "error",
            ],
        )
        w.writeheader()

        for input_file in input_files:
            fmt = detect_format(input_file)
            if "MarQSim_dataset" in str(input_file):
                dataset = "MarQSim_dataset"
            elif "Genesis_dataset" in str(input_file):
                dataset = "Genesis_dataset"
            else:
                dataset = "custom"

            try:
                ph = parse_hamiltonian_file(
                    input_file, keep_identity=args.keep_identity, reverse_labels=args.reverse_labels
                )
            except Exception as e:
                w.writerow(
                    {
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "order_method": args.order_method,
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "n_terms": "",
                        "n_qubits": "",
                        "ok": False,
                        "wall_s": 0.0,
                        "depth": "",
                        "gates_total": "",
                        "cx": "",
                        "twoq_total": "",
                        "ops_json": "",
                        "error": f"parse failed: {e}",
                    }
                )
                csvf.flush()
                continue

            if args.max_terms and args.max_terms > 0 and ph.n_terms > args.max_terms:
                w.writerow(
                    {
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "order_method": args.order_method,
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "n_terms": ph.n_terms,
                        "n_qubits": ph.n_qubits,
                        "ok": False,
                        "wall_s": 0.0,
                        "depth": "",
                        "gates_total": "",
                        "cx": "",
                        "twoq_total": "",
                        "ops_json": "",
                        "error": f"skipped (n_terms={ph.n_terms} > --max-terms={args.max_terms})",
                    }
                )
                csvf.flush()
                continue

            for tval in args.ts:
                t0 = time.time()
                ok = False
                depth = ""
                gates_total = ""
                cx = ""
                twoq_total = ""
                ops_json = ""
                ibm_depth = ""
                gates_opt_total = ""
                gates_opt_u1 = ""
                gates_opt_u2 = ""
                gates_opt_u3 = ""
                gates_opt_cx = ""
                gates_opt_json = ""
                err_s = ""
                try:
                    qc = phoenix_compile_to_circuit(
                        ph,
                        time_t=tval,
                        order_method=args.order_method,
                        qiskit_opt=(not args.no_qiskit_opt),
                    )

                    qc_ibm = None
                    ops_ibm = None
                    if not args.no_ibm_counts:
                        ibm_opt_level = 3 if (not args.no_qiskit_opt) else 0
                        qc_ibm, ops_ibm = _ibm_basis_gate_counts(qc, optimization_level=ibm_opt_level)

                    wall = time.time() - t0
                    ops = {str(k): int(v) for k, v in qc.count_ops().items()}
                    ok = True
                    depth = int(qc.depth())
                    gates_total = sum(ops.values())
                    cx = ops.get("cx", 0)
                    twoq_total = _count_two_qubit_gates(qc)
                    ops_json = json.dumps(ops, sort_keys=True)
                    if qc_ibm is not None and ops_ibm is not None:
                        ibm_depth = int(qc_ibm.depth())
                        gates_opt_total = sum(ops_ibm.values())
                        gates_opt_u1 = ops_ibm.get("U1", 0)
                        gates_opt_u2 = ops_ibm.get("U2", 0)
                        gates_opt_u3 = ops_ibm.get("U3", 0)
                        gates_opt_cx = ops_ibm.get("CX", 0)
                        gates_opt_json = json.dumps(ops_ibm, sort_keys=True)
                except Exception as e:
                    wall = time.time() - t0
                    err_s = str(e)

                w.writerow(
                    {
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": tval,
                        "order_method": args.order_method,
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "n_terms": ph.n_terms,
                        "n_qubits": ph.n_qubits,
                        "qubits": ph.n_qubits,
                        "ok": ok,
                        "wall_s": f"{wall:.6f}",
                        "depth": depth,
                        "gates_total": gates_total,
                        "cx": cx,
                        "twoq_total": twoq_total,
                        "ops_json": ops_json,
                        "ibm_depth": ibm_depth,
                        "gates_opt_total": gates_opt_total,
                        "gates_opt_U1": gates_opt_u1,
                        "gates_opt_U2": gates_opt_u2,
                        "gates_opt_U3": gates_opt_u3,
                        "gates_opt_CX": gates_opt_cx,
                        "gates_opt_json": gates_opt_json,
                        "error": err_s,
                    }
                )
                csvf.flush()

                status = "OK" if ok else "WARN"
                print(
                    f"{status}: {input_file.name} t={tval} order={args.order_method} wall_s={wall:.2f}",
                    file=sys.stderr,
                )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
