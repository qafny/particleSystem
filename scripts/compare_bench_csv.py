#!/usr/bin/env python3
"""
Join qblue_bench.py and a baseline CSV into a single wide CSV.

This is meant to make resource/time comparisons easy in spreadsheets without
manual merging.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path


def _canon_t(t: str) -> str:
    try:
        return f"{float(t):.12g}"
    except Exception:
        return t.strip()


def _key(row: dict[str, str]) -> tuple[str, str, str, str]:
    return (
        row.get("dataset", "").strip(),
        row.get("format", "").strip(),
        row.get("input_name", "").strip(),
        _canon_t(row.get("t", "")),
    )


def _float_or_empty(s: str) -> float | None:
    s = (s or "").strip()
    if not s:
        return None
    try:
        return float(s)
    except Exception:
        return None


def _int_or_empty(s: str) -> int | None:
    s = (s or "").strip()
    if not s:
        return None
    try:
        return int(float(s))
    except Exception:
        return None


def _ratio(num: str, den: str) -> str:
    n = _float_or_empty(num)
    d = _float_or_empty(den)
    if n is None or d is None or d == 0:
        return ""
    return f"{n / d:.6g}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qblue", type=Path, default=Path("results/qblue.csv"))
    ap.add_argument(
        "--phoenix",
        type=Path,
        default=Path("results/phoenix.csv"),
        help="Back-compat alias for --baseline (defaults to results/phoenix.csv).",
    )
    ap.add_argument("--baseline", type=Path, default=None, help="Baseline CSV to compare against QBlue.")
    ap.add_argument(
        "--baseline-name",
        type=str,
        default=None,
        help="Column prefix for the baseline (e.g. phoenix, paulihedral, tetris).",
    )
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    baseline_path = args.baseline or args.phoenix
    baseline_name = (args.baseline_name or ("baseline" if args.baseline else "phoenix")).strip()
    if not baseline_name:
        raise SystemExit("--baseline-name must not be empty.")

    if args.out is None:
        if baseline_name == "phoenix" and args.baseline is None:
            args.out = Path("results/qblue_vs_phoenix.csv")
        else:
            args.out = Path(f"results/qblue_vs_{baseline_name}.csv")

    qblue_rows: list[dict[str, str]] = []
    with args.qblue.open("r", newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            row["t"] = _canon_t(row.get("t", ""))
            qblue_rows.append(row)

    baseline_map: dict[tuple[str, str, str, str], dict[str, str]] = {}
    with baseline_path.open("r", newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            row["t"] = _canon_t(row.get("t", ""))
            k = _key(row)
            baseline_map.setdefault(k, row)

    fieldnames = [
        "dataset",
        "format",
        "input_name",
        "t",
        # QBlue knobs
        "qblue_err",
        "qblue_pipeline",
        "qblue_grouping",
        "qblue_algorithm",
        "qblue_backend",
        # QBlue metrics
        "qblue_ok",
        "qblue_compile_s",
        "qblue_wall_s",
        "qblue_qubits",
        "qblue_gates_opt_total",
        "qblue_gates_opt_CX",
        # Baseline knobs
        f"{baseline_name}_compiler",
        f"{baseline_name}_order_method",
        f"{baseline_name}_qiskit_opt",
        f"{baseline_name}_reverse_labels",
        # Baseline metrics
        f"{baseline_name}_ok",
        f"{baseline_name}_compile_s",
        f"{baseline_name}_wall_s",
        f"{baseline_name}_qubits",
        f"{baseline_name}_depth",
        f"{baseline_name}_gates_opt_total",
        f"{baseline_name}_gates_opt_CX",
        # Ratios (baseline / qblue)
        "ratio_compile_s",
        "ratio_wall_s",
        "ratio_gates_opt_total",
        "ratio_gates_opt_CX",
        # Debug tails
        "qblue_stderr_tail",
        f"{baseline_name}_error",
    ]

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()

        for qb in qblue_rows:
            k = _key(qb)
            bl = baseline_map.get(k, {})

            qb_gates_opt_total = qb.get("gates_opt_total", "")
            qb_gates_opt_cx = qb.get("gates_opt_CX", "")

            # Baselines prefer the IBM-basis "gates_opt_*" columns if present.
            bl_gates_opt_total = bl.get("gates_opt_total", "") or bl.get("gates_total", "")
            bl_gates_opt_cx = bl.get("gates_opt_CX", "") or bl.get("cx", "")

            w.writerow(
                {
                    "dataset": qb.get("dataset", ""),
                    "format": qb.get("format", ""),
                    "input_name": qb.get("input_name", ""),
                    "t": qb.get("t", ""),
                    "qblue_err": qb.get("err", ""),
                    "qblue_pipeline": qb.get("pipeline", ""),
                    "qblue_grouping": qb.get("grouping", ""),
                    "qblue_algorithm": qb.get("algorithm", ""),
                    "qblue_backend": qb.get("backend", ""),
                    "qblue_ok": qb.get("ok", ""),
                    "qblue_compile_s": qb.get("compile_s", ""),
                    "qblue_wall_s": qb.get("wall_s", ""),
                    "qblue_qubits": qb.get("qubits", ""),
                    "qblue_gates_opt_total": qb_gates_opt_total,
                    "qblue_gates_opt_CX": qb_gates_opt_cx,
                    f"{baseline_name}_compiler": bl.get("compiler", ""),
                    f"{baseline_name}_order_method": bl.get("order_method", ""),
                    f"{baseline_name}_qiskit_opt": bl.get("qiskit_opt", ""),
                    f"{baseline_name}_reverse_labels": bl.get("reverse_labels", ""),
                    f"{baseline_name}_ok": bl.get("ok", ""),
                    f"{baseline_name}_compile_s": bl.get("compile_s", ""),
                    f"{baseline_name}_wall_s": bl.get("wall_s", ""),
                    f"{baseline_name}_qubits": bl.get("qubits", "") or bl.get("n_qubits", ""),
                    f"{baseline_name}_depth": bl.get("ibm_depth", "") or bl.get("depth", ""),
                    f"{baseline_name}_gates_opt_total": bl_gates_opt_total,
                    f"{baseline_name}_gates_opt_CX": bl_gates_opt_cx,
                    "ratio_compile_s": _ratio(bl.get("compile_s", ""), qb.get("compile_s", "")),
                    "ratio_wall_s": _ratio(bl.get("wall_s", ""), qb.get("wall_s", "")),
                    "ratio_gates_opt_total": _ratio(bl_gates_opt_total, qb_gates_opt_total),
                    "ratio_gates_opt_CX": _ratio(bl_gates_opt_cx, qb_gates_opt_cx),
                    "qblue_stderr_tail": qb.get("stderr_tail", ""),
                    f"{baseline_name}_error": bl.get("error", ""),
                }
            )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
