"""Render the original comparison figures from the shared CSV schema."""

import argparse
from pathlib import Path

from benchmark import ROOT
import plot_style as style

KEY = ["file_name", "error", "time", "path_flag"]


def load(path):
    frame = style.pd.read_csv(path)
    frame = frame[frame.status == "ok"].copy()
    if frame.duplicated(KEY).any():
        raise ValueError(f"Duplicate experiment keys in {path}")
    frame["input_name"] = frame.file_name
    frame["dataset"] = style.np.select(
        [frame.program_size < 100, frame.program_size < 1200], ["S", "M"], default="L")
    frame["err"] = frame.error
    frame["t"] = frame.time
    frame["n_terms"] = frame.program_size
    frame["wall_s"] = frame.compilation_time
    frame["qblue_full_total"] = frame.single_qubit_gates + frame.multi_qubit_gates
    frame["qblue_pre_total"] = frame.single_qubit_gates_bfopt + frame.multi_qubit_gates_bfopt
    frame["pipeline"] = frame.path_flag.map({1: "std", 3: "qdrift"})
    return frame


def join(qblue, baseline, name):
    columns = KEY + ["single_qubit_gates", "multi_qubit_gates",
                     "single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]
    renamed = baseline[columns].rename(columns={c: f"{name}_{c}" for c in columns if c not in KEY})
    merged = qblue.merge(renamed, on=KEY, validate="one_to_one")
    merged[f"{name}_fair_total"] = merged[f"{name}_single_qubit_gates"] + merged[f"{name}_multi_qubit_gates"]
    merged[f"{name}_fair_pre_total"] = merged[f"{name}_single_qubit_gates_bfopt"] + merged[f"{name}_multi_qubit_gates_bfopt"]
    return merged


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv-dir", type=Path, default=ROOT / "results")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results/plots")
    args = parser.parse_args()
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
            for name, frame in merged.items():
                if frame.empty:
                    continue
                style.plot_scatter_vs_competitor(frame, name, name.title(),
                    out / f"fig2_scatter_qblue_vs_{name}_err{error}.png", err_label=str(error))
        for name, baseline in baselines.items():
            merged = join(std, baseline, name)
            if not merged.empty:
                style.plot_gate_reduction(merged, name, name.title(),
                    out / f"tab2_gate_reduction_{name}.png", t_label=label)
        digital = all_rows[all_rows.path_flag == 1]
        analog = all_rows[all_rows.path_flag == 11].copy()
        analog["path_flag"] = 1
        columns = KEY + ["single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]
        matched = digital.merge(analog[columns], on=KEY, suffixes=("_ibm", "_ind"), validate="one_to_one")
        for column, label in [("single_qubit_gates_bfopt", "1-qubit"), ("multi_qubit_gates_bfopt", "multi-qubit")]:
            style.plot_analog_vs_digital_polar(matched, column + "_ibm", column + "_ind", label,
                out / f"tab_analog_vs_digital_{label}_polar.png")


if __name__ == "__main__":
    main()
