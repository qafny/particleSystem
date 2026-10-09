"""Summarize results/*.csv into results/tables.md.

1. Trotter compilation at the same step count: QBlue vs OpenFermion (as generated
   and after Qiskit O3) and PHOENIX, per Trotter step.
2. Best QBlue algorithm vs OpenFermion / PHOENIX second-order Trotter, each at the
   step count it would use (OpenFermion's own bound for both baselines).
3. Second-order step counts: QBlue's bound vs OpenFermion's.
4. Algorithms inside QBlue and digital vs analog targets.
"""

import argparse
import csv
import statistics
from pathlib import Path

from benchmark import ROOT

ALGORITHMS = {1: "Trotter-1", 2: "Trotter-2", 3: "QDrift", 6: "MarQSim (CNOT)", 7: "MarQSim (CNOT+1q)"}


def load(path):
    if not path.exists():
        return {}
    with path.open(newline="") as source:
        rows = [r for r in csv.DictReader(source) if r["status"] == "ok"]
    return {(r["file_name"], int(r["path_flag"])): r for r in rows}


def num(row, field):
    return float(row[field])


def name(path):
    return (Path(path).stem.replace("_sto3g", "").replace("_spin_orbitals_Hamiltonian", "")
            .replace("_electrons", "e").replace("_paulis", "p"))


def saving(ours, base):
    return 1 - ours / base


def fmt(x):
    return f"{x:.3g}" if x >= 1e6 else f"{round(x):,}"


def summary(label, values):
    if not values:
        return f"{label}: no data."
    return (f"{label}: mean {100 * statistics.mean(values):.1f}%, "
            f"max {100 * max(values):.1f}%, min {100 * min(values):.1f}% ({len(values)} Hamiltonians).")


def compilation_table(qblue, of, phx, order):
    lines = [f"### Trotter-{order}: gates per Trotter step at the same step count\n",
             "| Hamiltonian | terms | OpenFermion CX | OpenFermion + O3 CX | PHOENIX CX | QBlue CX | QBlue total | OpenFermion total | CX saving vs OpenFermion | total saving vs OpenFermion |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    cx_saving, total_saving = [], []
    for key, q in sorted(qblue.items()):
        if key[1] != order or key not in of:
            continue
        r = num(q, "trotter_step")
        o, p = of[key], phx.get(key)
        q_cx, q_tot = num(q, "multi_qubit_gates") / r, (num(q, "multi_qubit_gates") + num(q, "single_qubit_gates")) / r
        o_cx = num(o, "multi_qubit_gates_bfopt") / r
        o_tot = (num(o, "multi_qubit_gates_bfopt") + num(o, "single_qubit_gates_bfopt")) / r
        o3_cx = num(o, "multi_qubit_gates") / r
        p_cx = f"{fmt(num(p, 'multi_qubit_gates') / r)}" if p else "–"
        cx_saving.append(saving(q_cx, o_cx))
        total_saving.append(saving(q_tot, o_tot))
        lines.append(f"| {name(key[0])} | {q['program_size']} | {fmt(o_cx)} | {fmt(o3_cx)} | {p_cx} | {fmt(q_cx)} | "
                     f"{fmt(q_tot)} | {fmt(o_tot)} | {100 * cx_saving[-1]:.1f}% | {100 * total_saving[-1]:.1f}% |")
    lines += ["", summary("CX saving vs OpenFermion", cx_saving), summary("Total-gate saving vs OpenFermion", total_saving), ""]
    return lines


def best_algorithm_table(qblue, of, phx, bounds):
    lines = ["### Best QBlue algorithm vs Trotterization in OpenFermion and PHOENIX\n",
             "OpenFermion and PHOENIX run second-order Trotter with OpenFermion's recommended step count "
             "(its tight bound; loose where the tight bound was not computed). QBlue uses the cheapest of its "
             "algorithms at its own error bounds. CNOT counts.\n",
             "| Hamiltonian | terms | r (OpenFermion) | OpenFermion | PHOENIX | QBlue best | saving vs OpenFermion | saving vs PHOENIX |",
             "|---|---|---|---|---|---|---|---|"]
    vs_of, vs_phx = [], []
    for (file_name, path), b in sorted(bounds.items()):
        key = (file_name, 2)
        if key not in of or key not in phx:
            continue
        r_of = int(b["of_r2_tight"] or b["of_r2_loose"])
        r_q = num(of[key], "trotter_step")
        of_cx = num(of[key], "multi_qubit_gates_bfopt") / r_q * r_of
        phx_cx = num(phx[key], "multi_qubit_gates") / r_q * r_of
        options = {p: num(qblue[(file_name, p)], "multi_qubit_gates") for p in ALGORITHMS if (file_name, p) in qblue}
        best = min(options, key=options.get)
        vs_of.append(saving(options[best], of_cx))
        vs_phx.append(saving(options[best], phx_cx))
        kind = "" if b["of_r2_tight"] else " (loose)"
        lines.append(f"| {name(file_name)} | {b['nterms']} | {r_of}{kind} | {fmt(of_cx)} | {fmt(phx_cx)} | "
                     f"{fmt(options[best])} ({ALGORITHMS[best]}) | {100 * vs_of[-1]:.1f}% | {100 * vs_phx[-1]:.1f}% |")
    lines += ["", summary("Saving vs OpenFermion", vs_of), summary("Saving vs PHOENIX", vs_phx), ""]
    return lines


def bounds_table(qblue, of, bounds):
    lines = ["### Second-order step counts: QBlue's bound vs OpenFermion's\n",
             "QBlue: Childs et al. Prop. F.4 with λ = Σ|h_j| (a guaranteed bound). "
             "OpenFermion: Poulin et al. leading-order estimate via `error_bound` and "
             "`trotter_steps_required_propagator`.\n",
             "| Hamiltonian | terms | r QBlue | r OpenFermion (tight) | r OpenFermion (loose) | QBlue CX at its r | QBlue CX at OpenFermion's r | OpenFermion CX at its r |",
             "|---|---|---|---|---|---|---|---|"]
    for (file_name, path), b in sorted(bounds.items()):
        key = (file_name, 2)
        if key not in qblue or key not in of:
            continue
        r_q = num(qblue[key], "trotter_step")
        r_of = int(b["of_r2_tight"] or b["of_r2_loose"])
        q_step = num(qblue[key], "multi_qubit_gates") / r_q
        of_step = num(of[key], "multi_qubit_gates_bfopt") / r_q
        lines.append(f"| {name(file_name)} | {b['nterms']} | {int(r_q):,} | {b['of_r2_tight'] or '–'} | {b['of_r2_loose']} | "
                     f"{fmt(q_step * r_q)} | {fmt(q_step * r_of)} | {fmt(of_step * r_of)} |")
    return lines + [""]


def algorithm_summary(qblue):
    def total(row):
        return num(row, "multi_qubit_gates") + num(row, "single_qubit_gates")

    files = sorted({f for f, _ in qblue})
    pairs = [("QDrift vs Trotter-1", 3, 1), ("QDrift vs Trotter-2", 3, 2), ("Trotter-2 vs Trotter-1", 2, 1),
             ("MarQSim (CNOT) vs QDrift", 6, 3), ("MarQSim (CNOT+1q) vs QDrift", 7, 3)]
    lines = ["### Algorithms inside QBlue (total gates, IBM digital)\n"]
    for label, ours, base in pairs:
        values = [saving(total(qblue[(f, ours)]), total(qblue[(f, base)]))
                  for f in files if (f, ours) in qblue and (f, base) in qblue]
        lines.append("- " + summary(label, values))
    lines += ["", "### Analog vs digital targets (multi-qubit terms)\n"]
    for label, offset in (("Indiana analog vs IBM digital", 10),):
        for path in (1, 2, 3, 6):
            values = [saving(num(qblue[(f, path + offset)], "multi_qubit_gates"), num(qblue[(f, path)], "multi_qubit_gates"))
                      for f in files if (f, path) in qblue and (f, path + offset) in qblue
                      and num(qblue[(f, path)], "multi_qubit_gates") > 0]
            lines.append("- " + summary(f"{label}, {ALGORITHMS[path]}", values))
    return lines + [""]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    qblue = load(args.csv_dir / "qblue_results.csv")
    of = load(args.csv_dir / "openfermion_results.csv")
    phx = load(args.csv_dir / "phoenix_results.csv")
    bounds_csv = args.csv_dir / "bounds_results.csv"
    bounds = {}
    if bounds_csv.exists():
        with bounds_csv.open(newline="") as source:
            bounds = {(r["file_name"], 2): r for r in csv.DictReader(source) if r["status"] == "ok"}
    lines = ["# Results\n", "ε = 0.1, t = π/4 unless the job file says otherwise; all-to-all connectivity.\n"]
    lines += compilation_table(qblue, of, phx, 1) + compilation_table(qblue, of, phx, 2)
    lines += best_algorithm_table(qblue, of, phx, bounds) + bounds_table(qblue, of, bounds)
    lines += algorithm_summary(qblue)
    out = args.csv_dir / "tables.md"
    out.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
