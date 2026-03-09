#!/usr/bin/env python3
"""
Benchmark a vendored OpenFermion baseline on QBlue datasets.

This script parses MarQSim/Genesis Hamiltonian text files into Pauli strings +
coefficients, constructs an OpenFermion QubitOperator, trotterizes it via
OpenFermion's gate-stream API, translates that stream into a qiskit circuit,
and writes a CSV with wall-clock time and gate/qubit counts.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OPENFERMION_DIR = ROOT / "thirdparty" / "OpenFermion"

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


def _require_deps() -> None:
    if not OPENFERMION_DIR.exists():
        raise FileNotFoundError(
            f"Missing {OPENFERMION_DIR}.\n"
            "Clone OpenFermion into thirdparty/ first, e.g.\n"
            "  git clone https://github.com/quantumlib/OpenFermion thirdparty/OpenFermion"
        )

    # OpenFermion imports matplotlib transitively through cirq. Point it to a
    # writable temp directory to avoid user-home cache warnings.
    mpl_dir = Path(tempfile.gettempdir()) / "particleSystem_openfermion_mplconfig"
    mpl_dir.mkdir(parents=True, exist_ok=True)
    os.environ.setdefault("MPLCONFIGDIR", str(mpl_dir))

    sys.path.insert(0, str(OPENFERMION_DIR / "src"))

    try:
        import qiskit  # noqa: F401
    except ModuleNotFoundError as e:
        raise ModuleNotFoundError("Missing Python dependency: qiskit.") from e

    try:
        import openfermion  # noqa: F401
    except ModuleNotFoundError as e:
        raise ModuleNotFoundError(
            "Could not import `openfermion` from thirdparty/OpenFermion/src.\n"
            f"Import failed due to missing dependency: {e.name!r}"
        ) from e


def _count_two_qubit_gates(qc) -> int:
    count = 0
    for inst in qc.data:
        op = inst.operation
        if getattr(op, "num_qubits", 0) >= 2:
            count += 1
    return count


def _ibm_basis_gate_counts(qc, *, optimization_level: int):
    from qiskit import transpile

    qc_ibm = transpile(qc, basis_gates=["u1", "u2", "u3", "cx"], optimization_level=optimization_level)
    ops = {str(k).upper(): int(v) for k, v in qc_ibm.count_ops().items()}
    return qc_ibm, ops


def _build_openfermion_operator(ph: ParsedHamiltonian):
    from openfermion import QubitOperator

    op = QubitOperator()
    for label, coeff in zip(ph.paulis, ph.coeffs):
        if abs(coeff.imag) > 1e-12:
            raise ValueError(f"OpenFermion trotter baseline requires real coefficients; got {coeff!r}")
        pieces = [f"{gate}{idx}" for idx, gate in enumerate(label) if gate != "I"]
        term = " ".join(pieces)
        op += QubitOperator(term, float(coeff.real))
    if len(op.terms) == 0:
        raise ValueError("No non-identity Hamiltonian terms remain after filtering")
    return op


def _gate_stream_to_qiskit(gate_lines: list[str], n_qubits: int):
    from qiskit import QuantumCircuit

    qc = QuantumCircuit(n_qubits)
    for line in gate_lines:
        parts = line.split()
        if not parts:
            continue
        gate = parts[0]
        if gate == "H":
            qc.h(int(parts[1]))
        elif gate == "Rx":
            qc.rx(float(parts[1]), int(parts[2]))
        elif gate == "Rz":
            qc.rz(float(parts[1]), int(parts[2]))
        elif gate == "CNOT":
            qc.cx(int(parts[1]), int(parts[2]))
        elif gate == "C-Phase":
            qc.cp(float(parts[1]), int(parts[2]), int(parts[3]))
        else:
            raise ValueError(f"Unsupported OpenFermion gate: {line}")
    return qc


def openfermion_compile_to_circuit(
    ph: ParsedHamiltonian,
    *,
    time_t: float,
    trotter_number: int,
    trotter_order: int,
):
    from openfermion import trotterize_exp_qubop_to_qasm

    op = _build_openfermion_operator(ph)
    gate_lines = list(
        trotterize_exp_qubop_to_qasm(
            op,
            evolution_time=float(time_t),
            trotter_number=int(trotter_number),
            trotter_order=int(trotter_order),
        )
    )
    qc = _gate_stream_to_qiskit(gate_lines, ph.n_qubits)
    return qc, {"qasm_gate_count": len(gate_lines)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["marqsim", "genesis", "all"], default="marqsim")
    ap.add_argument("--inputs", nargs="+", type=Path, default=None, help="Explicit list of input files.")
    ap.add_argument("--out", type=Path, default=Path("results/openfermion.csv"))
    ap.add_argument("--ts", nargs="+", type=float, default=[0.1], help="Evolution time(s) to benchmark.")
    ap.add_argument("--no-qiskit-opt", action="store_true", help="Disable the final Qiskit optimization/transpile.")
    ap.add_argument(
        "--no-ibm-counts",
        action="store_true",
        help="Skip transpiling to the IBM (u1/u2/u3/cx) basis for QBlue-comparable counts.",
    )
    ap.add_argument(
        "--trotter-number",
        type=int,
        default=1,
        help="Number of Trotter steps passed to OpenFermion.",
    )
    ap.add_argument(
        "--trotter-order",
        type=int,
        choices=[1, 2, 3],
        default=1,
        help="Trotter order passed to OpenFermion.",
    )
    ap.add_argument("--reverse-labels", action="store_true", help="Reverse Pauli strings before synthesis.")
    ap.add_argument(
        "--keep-identity",
        action="store_true",
        help="Keep all-'I' terms (normally dropped as they only contribute global phase).",
    )
    ap.add_argument("--limit", type=int, default=0, help="Limit number of input files (0 = no limit).")
    ap.add_argument(
        "--max-terms",
        type=int,
        default=5000,
        help="Skip Hamiltonians with more than this many terms (0 = no limit).",
    )
    args = ap.parse_args()

    try:
        _require_deps()
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
                "compiler",
                "dataset",
                "format",
                "input_path",
                "input_name",
                "t",
                "qiskit_opt",
                "reverse_labels",
                "trotter_number",
                "trotter_order",
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
                "qasm_gate_count",
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
                        "compiler": "openfermion",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "trotter_number": args.trotter_number,
                        "trotter_order": args.trotter_order,
                        "n_terms": "",
                        "n_qubits": "",
                        "qubits": "",
                        "ok": False,
                        "wall_s": 0.0,
                        "depth": "",
                        "gates_total": "",
                        "cx": "",
                        "twoq_total": "",
                        "ops_json": "",
                        "ibm_depth": "",
                        "gates_opt_total": "",
                        "gates_opt_U1": "",
                        "gates_opt_U2": "",
                        "gates_opt_U3": "",
                        "gates_opt_CX": "",
                        "gates_opt_json": "",
                        "qasm_gate_count": "",
                        "error": f"parse failed: {e}",
                    }
                )
                csvf.flush()
                continue

            if args.max_terms and args.max_terms > 0 and ph.n_terms > args.max_terms:
                w.writerow(
                    {
                        "compiler": "openfermion",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "trotter_number": args.trotter_number,
                        "trotter_order": args.trotter_order,
                        "n_terms": ph.n_terms,
                        "n_qubits": ph.n_qubits,
                        "qubits": ph.n_qubits,
                        "ok": False,
                        "wall_s": 0.0,
                        "depth": "",
                        "gates_total": "",
                        "cx": "",
                        "twoq_total": "",
                        "ops_json": "",
                        "ibm_depth": "",
                        "gates_opt_total": "",
                        "gates_opt_U1": "",
                        "gates_opt_U2": "",
                        "gates_opt_U3": "",
                        "gates_opt_CX": "",
                        "gates_opt_json": "",
                        "qasm_gate_count": "",
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
                qasm_gate_count = ""
                err_s = ""

                try:
                    qc, meta = openfermion_compile_to_circuit(
                        ph,
                        time_t=tval,
                        trotter_number=args.trotter_number,
                        trotter_order=args.trotter_order,
                    )
                    wall = time.time() - t0
                    ops = {str(k): int(v) for k, v in qc.count_ops().items()}
                    ok = True
                    depth = int(qc.depth())
                    gates_total = sum(ops.values())
                    cx = ops.get("cx", 0)
                    twoq_total = _count_two_qubit_gates(qc)
                    ops_json = json.dumps(ops, sort_keys=True)
                    qasm_gate_count = meta.get("qasm_gate_count", "")

                    if not args.no_ibm_counts:
                        ibm_opt_level = 3 if (not args.no_qiskit_opt) else 0
                        qc_ibm, ops_ibm = _ibm_basis_gate_counts(qc, optimization_level=ibm_opt_level)
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
                        "compiler": "openfermion",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": tval,
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
                        "trotter_number": args.trotter_number,
                        "trotter_order": args.trotter_order,
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
                        "qasm_gate_count": qasm_gate_count,
                        "error": err_s,
                    }
                )
                csvf.flush()

                status = "OK" if ok else "WARN"
                print(
                    (
                        f"{status}: {input_file.name} t={tval} "
                        f"trotter={args.trotter_order}/{args.trotter_number} wall_s={wall:.2f}"
                    ),
                    file=sys.stderr,
                )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
