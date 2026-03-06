#!/usr/bin/env python3
"""
Benchmark the vendored Paulihedral baseline (thirdparty/phoenix) on QBlue datasets.

This uses the Paulihedral implementation integrated in Phoenix's repo (it lives
under the `tetris.*` Python package there) and emits QBlue-comparable IBM-basis
gate counts (u1/u2/u3/cx).
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


def _group_paulis_and_coeffs(paulis: list[str], coeffs: list[complex]) -> list[tuple[tuple[int, ...], list[str], list[complex]]]:
    """
    Group Pauli strings by their nontrivial parts (same idea as Phoenix's grouping).

    Returns a list of (support_indices, group_paulis, group_coeffs) in a stable order.
    """

    groups: dict[tuple[int, ...], list[tuple[str, complex]]] = {}
    for p, c in zip(paulis, coeffs):
        idx = tuple(i for i, ch in enumerate(p) if ch != "I")
        groups.setdefault(idx, []).append((p, c))

    # Sort groups by descending locality, then lexicographically.
    groups = dict(sorted(groups.items(), key=lambda kv: (-len(kv[0]), kv[0])))

    # Reorder equal-locality groups to reduce overlap (greedy).
    groups_on_length: dict[int, list[tuple[int, ...]]] = {}
    for idx in groups.keys():
        groups_on_length.setdefault(len(idx), []).append(idx)

    def overlap_score(idx: tuple[int, ...], selected: list[tuple[int, ...]]) -> int:
        s = 0
        set_idx = set(idx)
        for eidx in selected:
            s += len(set_idx & set(eidx))
        return s

    ordered: list[tuple[int, ...]] = []
    for _, indices in sorted(groups_on_length.items(), key=lambda kv: -kv[0]):
        selected_equal: list[tuple[int, ...]] = []
        remaining = list(indices)
        while remaining:
            best = min(remaining, key=lambda idx: overlap_score(idx, selected_equal))
            selected_equal.append(best)
            remaining.remove(best)
        ordered.extend(selected_equal)

    out: list[tuple[tuple[int, ...], list[str], list[complex]]] = []
    for idx in ordered:
        pcs = groups[idx]
        out.append((idx, [p for p, _ in pcs], [c for _, c in pcs]))
    return out


def _require_deps() -> None:
    if not PHOENIX_DIR.exists():
        raise FileNotFoundError(
            f"Missing {PHOENIX_DIR}.\n"
            "Clone Phoenix into thirdparty/ first, e.g.\n"
            "  git clone https://github.com/iqubit-org/phoenix thirdparty/phoenix"
        )

    sys.path.insert(0, str(PHOENIX_DIR))
    import qiskit  # noqa: F401
    import tetris  # noqa: F401


def _all2all_pgraph(n_qubits: int):
    import numpy as np

    from tetris.utils.hardware import pGraph

    # Directed complete graph (excluding self-loops).
    G = np.ones((n_qubits, n_qubits), dtype=float)
    np.fill_diagonal(G, 0)
    C = np.ones((n_qubits, n_qubits), dtype=float)
    np.fill_diagonal(C, 0)
    return pGraph(G, C)


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


def paulihedral_compile_to_circuit(
    ph: ParsedHamiltonian,
    *,
    time_t: float,
    reverse_labels: bool,
) -> tuple[object, dict[str, object]]:
    from tetris.benchmark.mypauli import pauliString
    from tetris.synthesis_SC import block_opt_SC
    from tetris.utils.parallel_bl import gate_count_oriented_scheduling

    if not ph.paulis:
        raise ValueError("No Hamiltonian terms parsed")

    n = len(ph.paulis[0])
    if any(len(p) != n for p in ph.paulis):
        raise ValueError("Inconsistent Pauli string lengths in input")

    coeffs_scaled = [c * float(time_t) for c in ph.coeffs]
    grouped = _group_paulis_and_coeffs(ph.paulis, coeffs_scaled)
    blocks = [[pauliString(p, c) for p, c in zip(group_paulis, group_coeffs)] for _, group_paulis, group_coeffs in grouped]

    layers = gate_count_oriented_scheduling(blocks)
    graph = _all2all_pgraph(n)
    qc, total_swaps, total_cx = block_opt_SC(layers, graph=graph)
    return qc, {"swap_count": int(total_swaps), "cx_count": int(total_cx), "reverse_labels": reverse_labels}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["marqsim", "genesis", "all"], default="marqsim")
    ap.add_argument("--inputs", nargs="+", type=Path, default=None, help="Explicit list of input files.")
    ap.add_argument("--out", type=Path, default=Path("results/paulihedral.csv"))
    ap.add_argument("--ts", nargs="+", type=float, default=[0.1], help="Evolution time(s) to benchmark.")
    ap.add_argument("--no-qiskit-opt", action="store_true", help="Disable the final Qiskit optimization/transpile.")
    ap.add_argument(
        "--no-ibm-counts",
        action="store_true",
        help="Skip transpiling to the IBM (u1/u2/u3/cx) basis for QBlue-comparable counts.",
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
                "swap_count",
                "synth_cx_count",
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
                        "compiler": "paulihedral",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
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
                        "swap_count": "",
                        "synth_cx_count": "",
                        "error": f"parse failed: {e}",
                    }
                )
                csvf.flush()
                continue

            if args.max_terms and args.max_terms > 0 and ph.n_terms > args.max_terms:
                w.writerow(
                    {
                        "compiler": "paulihedral",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": "",
                        "qiskit_opt": not args.no_qiskit_opt,
                        "reverse_labels": args.reverse_labels,
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
                        "swap_count": "",
                        "synth_cx_count": "",
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
                swap_count = ""
                synth_cx_count = ""
                err_s = ""

                try:
                    qc, meta = paulihedral_compile_to_circuit(ph, time_t=tval, reverse_labels=args.reverse_labels)
                    wall = time.time() - t0
                    ops = {str(k): int(v) for k, v in qc.count_ops().items()}
                    ok = True
                    depth = int(qc.depth())
                    gates_total = sum(ops.values())
                    cx = ops.get("cx", 0)
                    twoq_total = _count_two_qubit_gates(qc)
                    ops_json = json.dumps(ops, sort_keys=True)
                    swap_count = meta.get("swap_count", "")
                    synth_cx_count = meta.get("cx_count", "")

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
                        "compiler": "paulihedral",
                        "dataset": dataset,
                        "format": fmt,
                        "input_path": str(input_file),
                        "input_name": input_file.name,
                        "t": tval,
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
                        "swap_count": swap_count,
                        "synth_cx_count": synth_cx_count,
                        "error": err_s,
                    }
                )
                csvf.flush()

                status = "OK" if ok else "WARN"
                print(f"{status}: {input_file.name} t={tval} wall_s={wall:.2f}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

