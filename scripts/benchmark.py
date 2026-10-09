"""Shared CSV contract and single-step cost measurement."""

import argparse
import csv
import math
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
os.environ.setdefault("MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "qblue-matplotlib"))
MAX_TERMS = 10000


@dataclass(frozen=True)
class ParsedHamiltonian:
    paulis: list[str]
    coeffs: list[complex]
    n_qubits: int


def parse_hamiltonian(path):
    paulis, coeffs = [], []
    n_qubits = None
    with path.open() as source:
        for number, line in enumerate(source, 1):
            if not line.strip():
                continue
            value, separator, label = line.partition("*")
            value = "".join(value.split())
            label = label.strip()
            if not separator or not value.startswith(("+", "-")) or not label or set(label) - set("IXYZ"):
                raise ValueError(f"{path}:{number}: expected signed coefficient * Pauli string")
            try:
                coefficient = float(value)
            except ValueError as error:
                raise ValueError(f"{path}:{number}: invalid coefficient") from error
            if not math.isfinite(coefficient):
                raise ValueError(f"{path}:{number}: expected a finite real coefficient")
            if n_qubits is not None and len(label) != n_qubits:
                raise ValueError(f"{path}:{number}: inconsistent Pauli string lengths")
            n_qubits = len(label)
            if coefficient and set(label) != {"I"}:
                paulis.append(label)
                coeffs.append(complex(coefficient))
    if not paulis:
        raise ValueError("No non-identity terms")
    return ParsedHamiltonian(paulis, coeffs, n_qubits)


def gate_counts(circuit):
    single = sum(item.operation.num_qubits == 1 for item in circuit.data)
    multi = sum(item.operation.num_qubits > 1 for item in circuit.data)
    return single, multi


def measure(compiler, optimize, hamiltonian, step_time, order):
    from qiskit import transpile

    started = perf_counter()
    circuit = compiler(hamiltonian, step_time, order)
    before = gate_counts(circuit)
    if optimize is not None:
        circuit = optimize(circuit)
    circuit = transpile(circuit, basis_gates=["u1", "u2", "u3", "cx"],
                        optimization_level=3, seed_transpiler=0)
    return before, gate_counts(circuit), perf_counter() - started


def run(name, compiler, optimize=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=ROOT / "results/qblue_results.csv")
    parser.add_argument("--output", type=Path, default=ROOT / f"results/{name}_results.csv")
    args = parser.parse_args()
    if args.input.resolve() == args.output.resolve():
        parser.error("Input and output must differ")
    with args.input.open(newline="") as source:
        reader = csv.DictReader(source)
        fields = reader.fieldnames
        rows = list(reader)
    if not fields or "trotter_step" not in fields:
        raise ValueError("Expected a qblue_result.csv schema")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cache = {}
    failures = 0
    with args.output.open("w", newline="") as target:
        writer = csv.DictWriter(target, fieldnames=fields)
        writer.writeheader()
        for reference in rows:
            # path 1 / 2: first- / second-order Trotter, repeated QBlue's trotter_step times
            order = int(reference["path_flag"])
            if order not in (1, 2):
                continue
            row = dict.fromkeys(fields, "")
            for field in ("file_name", "error", "time", "path_flag", "nqubit", "program_size", "trotter_step"):
                row[field] = reference[field]
            try:
                if reference["status"] != "ok":
                    raise ValueError("QBlue reference failed: " + reference["message"])
                repetitions = int(reference["trotter_step"])
                if repetitions < 1:
                    raise ValueError("Expected a positive repetition count")
                path = Path(reference["file_name"])
                if not path.is_absolute():
                    path = ROOT / "mlqblue" / path
                # One step is compiled with the full evolution time as its angle: tiny angles
                # (t / trotter_step) would let Qiskit O3 drop near-identity rotations.
                key = (path.resolve(), float(reference["time"]), order)
                if key not in cache:
                    hamiltonian = parse_hamiltonian(path)
                    if len(hamiltonian.paulis) > MAX_TERMS:
                        raise ValueError(f"Exceeds {MAX_TERMS} non-identity terms")
                    cache[key] = measure(compiler, optimize, hamiltonian, key[1], order)
                before, after, elapsed = cache[key]
                row.update(compilation_time=elapsed,
                           compilation_terms=int(reference["program_size"]) * repetitions,
                           single_qubit_gates=after[0] * repetitions,
                           multi_qubit_gates=after[1] * repetitions,
                           single_qubit_gates_bfopt=before[0] * repetitions,
                           multi_qubit_gates_bfopt=before[1] * repetitions,
                           status="ok")
            except Exception as error:
                row.update(status="error", message=str(error))
                failures += 1
            writer.writerow(row)
            target.flush()
            print(f"{name}: {row['file_name']}: {row['status']} {row['message']}", flush=True)
    return int(failures > 0)
