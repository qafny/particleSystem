"""Render the comparison figures from results/*.csv and results/savings.csv (written by tables.py)."""

import argparse
from pathlib import Path

from benchmark import ROOT
import plot_style as style

KEY = ["file_name", "error", "time", "path_flag"]
SUMMARY = [("E0", "Best QBlue vs OpenFermion (2nd order, OF steps)"),
           ("E0Q", "Best QBlue vs OpenFermion (2nd order, QBlue steps)"),
           ("E0P", "Best QBlue vs PHOENIX (1st order, QBlue steps)"),
           ("E3", "Best QBlue vs QBlue Trotter-1"),
           ("E1a", "Trotter-1, same steps: vs OpenFermion"),
           ("E1c", "Trotter-1, same steps: vs PHOENIX"),
           ("E2", "Trotter-2, own step functions: vs OpenFermion")]


def load(path):
    frame = style.pd.read_csv(path)
    frame = frame[frame.status == "ok"].copy()
    if frame.duplicated(KEY).any():
        raise ValueError(f"Duplicate experiment keys in {path}")
    frame["input_name"] = frame.file_name
    frame["dataset"] = frame.file_name.str.extract(r"/(small|middle|large)/")[0].map(
        {"small": "S", "middle": "M", "large": "L"})
    frame["err"] = frame.error
    frame["t"] = frame.time
    frame["n_terms"] = frame.program_size
    frame["wall_s"] = frame.compilation_time
    frame["qblue_full_total"] = frame.single_qubit_gates + frame.multi_qubit_gates
    frame["qblue_pre_total"] = frame.single_qubit_gates_bfopt + frame.multi_qubit_gates_bfopt
    frame["pipeline"] = frame.path_flag.map({1: "std", 3: "qdrift"})
    return frame


def join(qblue, baseline, name):
    """OpenFermion as generated (it has no optimizer); PHOENIX after its own optimization."""
    suffix = "_bfopt" if name == "openfermion" else ""
    columns = KEY + [f"single_qubit_gates{suffix}", f"multi_qubit_gates{suffix}"]
    merged = qblue.merge(baseline[columns], on=KEY, suffixes=("", f"_{name}"), validate="one_to_one")
    merged[f"{name}_fair_total"] = (merged[f"single_qubit_gates{suffix}_{name}"]
                                    + merged[f"multi_qubit_gates{suffix}_{name}"])
    return merged


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv-dir", type=Path, default=ROOT / "results")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results/plots")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    savings = style.pd.read_csv(args.csv_dir / "savings.csv")
    savings["time"] = savings.time.round(4)
    for t, name in ((0.1963, "pi16"), (0.7854, "pi4")):
        at = savings[savings.time == t]
        label = style.T_NAMES[t]
        style.plot_overall([("PHOENIX, ", "PHOENIX (1st order)", at[at.experiment == "E0P"]),
                            ("OpenFermion, ", "OpenFermion (2nd order)", at[at.experiment == "E0Q"])],
                           args.out_dir / f"fig13_overall_qblue_steps_{name}.png",
                           f"QBlue (best algorithm) vs. PHOENIX and OpenFermion, both at QBlue's step count (t = {label})",
                           "PHOENIX: first-order Trotter; OpenFermion: second-order Trotter; each repeated QBlue's step count of that order.")
        style.plot_overall([("", "OpenFermion (2nd order)", at[at.experiment == "E0"])],
                           args.out_dir / f"overall_openfermion_own_steps_{name}.png",
                           f"QBlue (best algorithm) vs. OpenFermion at OpenFermion's own step count (t = {label})",
                           "OpenFermion steps: error_bound + trotter_steps_required_propagator.")
    style.plot_summary(savings, SUMMARY, args.out_dir / "summary.png")

    qblue = load(args.csv_dir / "qblue_results.csv")
    baselines = {name: load(path) for name in ("phoenix", "openfermion")
                 if (path := args.csv_dir / f"{name}_results.csv").exists()}
    style.ERR_ORDER = sorted(qblue.error.unique())
    style.ERR_LABELS = {e: f"ε={e}" for e in style.ERR_ORDER}
    for time_value, all_rows in qblue.groupby("time"):
        out = args.out_dir / f"t{time_value}"
        out.mkdir(parents=True, exist_ok=True)
        label = f"t = {time_value}"
        style.T_LABEL_PI16 = label
        flower = all_rows.copy()
        flower["qblue_full_total"] = flower.qblue_pre_total
        style.plot_qdrift_vs_std_polar(flower, out / "fig_qdrift_vs_std_polar.png", t_label=label)
        std = all_rows[all_rows.path_flag == 1]
        for error, subset in std.groupby("error"):
            available = {name: frame[(frame.time == time_value) & (frame.error == error) & (frame.path_flag == 1)]
                         for name, frame in baselines.items()}
            merged = {name: join(subset, frame, name) for name, frame in available.items()}
            style.plot_gate_count(subset, merged.get("phoenix"), merged.get("openfermion"),
                                  out / f"tab2_gate_count_err{error}.png", err_label=str(error))
            style.plot_compile_time(subset, available.get("phoenix"), available.get("openfermion"),
                                    out / f"tab2_compile_time_err{error}.png", err_label=str(error))
        analog = all_rows[all_rows.path_flag == 11].copy()
        analog["path_flag"] = 1
        columns = KEY + ["single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]
        matched = std.merge(analog[columns], on=KEY, suffixes=("_ibm", "_ind"), validate="one_to_one")
        for column, label in [("single_qubit_gates_bfopt", "1-qubit"), ("multi_qubit_gates_bfopt", "multi-qubit")]:
            style.plot_analog_vs_digital_polar(matched, column + "_ibm", column + "_ind", label,
                out / f"tab_analog_vs_digital_{label}_polar.png")


if __name__ == "__main__":
    main()
