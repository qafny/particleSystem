#!/usr/bin/env python3
"""
Generate benchmark result plots for the QBlue paper.

Usage:
    python3 scripts/plot_results.py [--out-dir results/plots]

Produces:
    1. scatter_qblue_vs_phoenix.png   -- per-program CX gates, QBlue vs Phoenix×splitting_r
    2. scatter_compile_time.png       -- wall time vs n_terms, QBlue vs Phoenix vs OpenFermion
    3. lines_gates_vs_err.png         -- median CX gates vs error bound, by pipeline
    4. bars_algorithm_selection.png   -- which Trotter algorithm QBlue picks (std vs qdrift)
    5. box_gate_reduction.png         -- per-program CX reduction QBlue vs Phoenix×splitting_r
"""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
import pandas as pd

RESULTS = Path(__file__).resolve().parents[1] / "results"

DATASET_ORDER = ["S", "M", "L"]
DATASET_LABELS = {"S": "Small", "M": "Medium", "L": "Large"}
DATASET_COLORS = {"S": "#4C72B0", "M": "#DD8452", "L": "#55A868"}

ERR_ORDER = [0.02, 0.1, 0.5]
ERR_LABELS = {0.02: "ε=0.02", 0.1: "ε=0.1", 0.5: "ε=0.5"}


# ---------------------------------------------------------------------------
# Data loading helpers
# ---------------------------------------------------------------------------

def _load(path: Path) -> pd.DataFrame | None:
    if not path.exists():
        print(f"  [skip] {path.name} not found")
        return None
    df = pd.read_csv(path)
    df = df[df["ok"].astype(str).str.lower() == "true"].copy()
    # Normalize t to 6 significant figures so rows from different runs dedup correctly
    if "t" in df.columns:
        df["t"] = df["t"].round(6)
    return df if len(df) else None


def load_qblue(*paths: Path) -> pd.DataFrame | None:
    frames = [_load(p) for p in paths]
    frames = [f for f in frames if f is not None]
    return pd.concat(frames, ignore_index=True) if frames else None


def load_phoenix(*paths: Path) -> pd.DataFrame | None:
    frames = [_load(p) for p in paths]
    frames = [f for f in frames if f is not None]
    return pd.concat(frames, ignore_index=True) if frames else None


def join_qblue_phoenix(qb: pd.DataFrame, ph: pd.DataFrame) -> pd.DataFrame:
    """
    Join QBlue and Phoenix on (input_name, dataset, t).
    QBlue may have multiple rows per file (err × pipeline); Phoenix has one per (file, t).
    Result has one row per QBlue row, with Phoenix columns suffixed _ph.
    """
    ph_key = ph[["input_name", "dataset", "t",
                  "gates_opt_CX", "gates_opt_total",
                  "compile_s", "wall_s", "n_terms"]].copy()
    ph_key = ph_key.rename(columns={c: c + "_ph" for c in
                                    ["gates_opt_CX", "gates_opt_total",
                                     "compile_s", "wall_s", "n_terms"]})
    # keep first Phoenix row per (input_name, dataset, t)
    ph_key = ph_key.drop_duplicates(subset=["input_name", "dataset", "t"])
    merged = qb.merge(ph_key, on=["input_name", "dataset", "t"], how="inner")
    # QBlue gates_opt_CX/total are single-step; multiply by splitting_r for full circuit cost
    merged["qblue_full_CX"] = merged["gates_opt_CX"] * merged["splitting_r"]
    merged["qblue_full_total"] = merged["gates_opt_total"] * merged["splitting_r"]
    # fair Phoenix CX = single-step CX × splitting_r from QBlue
    merged["phoenix_fair_CX"] = merged["gates_opt_CX_ph"] * merged["splitting_r"]
    merged["phoenix_fair_total"] = merged["gates_opt_total_ph"] * merged["splitting_r"]
    return merged


# ---------------------------------------------------------------------------
# Plot 1: scatter QBlue vs Phoenix×r
# ---------------------------------------------------------------------------

def plot_scatter_vs_phoenix(merged: pd.DataFrame, out: Path) -> None:
    fig, ax = plt.subplots(figsize=(6, 6))

    for ds in DATASET_ORDER:
        sub = merged[merged["dataset"] == ds]
        if sub.empty:
            continue
        ax.scatter(
            sub["phoenix_fair_total"].clip(lower=1),
            sub["qblue_full_total"].clip(lower=1),
            label=DATASET_LABELS[ds],
            color=DATASET_COLORS[ds],
            alpha=0.6, s=18, linewidths=0,
        )

    lims = [1e1, max(merged["phoenix_fair_total"].max(), merged["qblue_full_total"].max()) * 2]
    ax.plot(lims, lims, "k--", linewidth=0.8, label="parity")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(lims)
    ax.set_ylim(lims)
    ax.set_xlabel("Phoenix  ×  splitting_r  (total gates)", fontsize=11)
    ax.set_ylabel("QBlue total gates", fontsize=11)
    ax.set_title("QBlue vs. Phoenix (error-adjusted)", fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which="both", linestyle=":", linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 2: compilation time vs n_terms
# ---------------------------------------------------------------------------

def plot_compile_time(qb: pd.DataFrame, ph: pd.DataFrame | None,
                      of: pd.DataFrame | None, out: Path,
                      err_label: str = "") -> None:
    fig, ax = plt.subplots(figsize=(7, 5))

    ax.scatter(qb["n_terms"], qb["wall_s"],
               color="#4C72B0", alpha=0.4, s=12, linewidths=0, label="QBlue")

    if ph is not None:
        ax.scatter(ph["n_terms"], ph["wall_s"],
                   color="#DD8452", alpha=0.5, s=12, linewidths=0, label="Phoenix")

    if of is not None:
        ax.scatter(of["n_terms"], of["wall_s"],
                   color="#55A868", alpha=0.5, s=12, linewidths=0, label="OpenFermion")

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Number of Pauli terms", fontsize=11)
    ax.set_ylabel("Wall time (s)", fontsize=11)
    title = f"Compilation time vs. Hamiltonian size  (ε={err_label})" if err_label else "Compilation time vs. Hamiltonian size"
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which="both", linestyle=":", linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 2b: gate count (total and CX) vs n_terms
# ---------------------------------------------------------------------------

def plot_gate_count(qb: pd.DataFrame, ph: pd.DataFrame | None,
                    of: pd.DataFrame | None, out: Path,
                    err_label: str = "") -> None:
    fig, ax = plt.subplots(figsize=(7, 5))

    # QBlue gate counts are single-step; multiply by splitting_r for full circuit cost
    qb = qb.copy()
    qb["gates_full_total"] = qb["gates_opt_total"] * qb["splitting_r"]

    ax.scatter(qb["n_terms"], qb["gates_full_total"],
               color="#4C72B0", alpha=0.4, s=12, linewidths=0, label="QBlue")
    if ph is not None and "gates_opt_total" in ph.columns:
        ax.scatter(ph["n_terms"], ph["gates_opt_total"],
                   color="#DD8452", alpha=0.5, s=12, linewidths=0, label="Phoenix")
    if of is not None and "gates_opt_total" in of.columns:
        ax.scatter(of["n_terms"], of["gates_opt_total"],
                   color="#55A868", alpha=0.5, s=12, linewidths=0, label="OpenFermion")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Number of Pauli terms", fontsize=11)
    ax.set_ylabel("Total gates", fontsize=11)
    title = f"Total gates vs. Hamiltonian size  (ε={err_label})" if err_label else "Total gates vs. Hamiltonian size"
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which="both", linestyle=":", linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 3: gate count vs error bound, per dataset
# ---------------------------------------------------------------------------

def plot_gates_vs_err(qb: pd.DataFrame, out: Path, t_label: str = "") -> None:
    errs_present = sorted(qb["err"].dropna().unique())
    if len(errs_present) < 2:
        print(f"  [skip] gates_vs_err: need ≥2 error values, have {errs_present}")
        return

    # QBlue gate counts are single-step; multiply by splitting_r for full circuit cost
    qb = qb.copy()
    qb["gates_full_CX"] = qb["gates_opt_CX"] * qb["splitting_r"]

    fig, axes = plt.subplots(1, len(DATASET_ORDER), figsize=(11, 4), sharey=True)

    for ax, ds in zip(axes, DATASET_ORDER):
        sub = qb[qb["dataset"] == ds]
        if sub.empty:
            ax.set_title(DATASET_LABELS[ds])
            continue
        for pipeline, ls in [("std", "-o"), ("qdrift", "--s")]:
            psub = sub[sub["pipeline"] == pipeline]
            if psub.empty:
                continue
            medians = psub.groupby("err")["gates_full_CX"].median().reindex(errs_present)
            ax.plot(range(len(errs_present)), medians.values,
                    ls, label=pipeline, markersize=5)
        ax.set_xticks(range(len(errs_present)))
        ax.set_xticklabels([ERR_LABELS.get(e, str(e)) for e in errs_present], fontsize=8)
        ax.set_yscale("log")
        ax.set_title(DATASET_LABELS.get(ds, ds), fontsize=11)
        ax.grid(True, axis="y", linestyle=":", linewidth=0.4)
        if ax is axes[0]:
            ax.set_ylabel("Median CX gates", fontsize=10)
            ax.legend(fontsize=8)

    title = f"Gate count vs. error bound  ({t_label})" if t_label else "Gate count vs. error bound"
    fig.suptitle(title, fontsize=12)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 4: algorithm selection stacked bar
# ---------------------------------------------------------------------------

def plot_algorithm_selection(qb: pd.DataFrame, out: Path) -> None:
    algos = qb["algorithm"].dropna().unique()
    if len(algos) < 2:
        print(f"  [skip] algorithm_selection: only one algorithm present ({algos})")
        return

    errs_present = sorted(qb["err"].dropna().unique())
    algo_labels = {
        "Trotterization (1st-order)": "1st order",
        "Trotterization (2nd-order)": "2nd order",
        "Trotterization (QDrift)": "QDrift",
        "Trotterization (MarQSim)": "MarQSim",
    }
    algo_colors = {
        "Trotterization (1st-order)": "#4C72B0",
        "Trotterization (2nd-order)": "#9467BD",
        "Trotterization (QDrift)":    "#DD8452",
        "Trotterization (MarQSim)":   "#55A868",
    }

    groups = [(ds, err) for ds in DATASET_ORDER for err in errs_present]
    group_labels = [f"{DATASET_LABELS.get(ds,ds)}\n{ERR_LABELS.get(err,err)}"
                    for ds, err in groups]

    # one row per (file, err) — deduplicate across pipelines by taking first
    deduped = qb.drop_duplicates(subset=["input_name", "dataset", "err", "t"])

    algo_order = [a for a in [
        "Trotterization (1st-order)", "Trotterization (2nd-order)",
        "Trotterization (QDrift)", "Trotterization (MarQSim)",
    ] if a in deduped["algorithm"].values]

    counts = {a: [] for a in algo_order}
    for ds, err in groups:
        sub = deduped[(deduped["dataset"] == ds) & (deduped["err"] == err)]
        for a in algo_order:
            counts[a].append((sub["algorithm"] == a).sum())

    fig, ax = plt.subplots(figsize=(max(8, len(groups) * 0.9), 4))
    x = np.arange(len(groups))
    bottom = np.zeros(len(groups))
    for a in algo_order:
        vals = np.array(counts[a], dtype=float)
        ax.bar(x, vals, bottom=bottom,
               label=algo_labels.get(a, a),
               color=algo_colors.get(a, "gray"))
        bottom += vals

    ax.set_xticks(x)
    ax.set_xticklabels(group_labels, fontsize=7)
    ax.set_ylabel("Number of programs", fontsize=10)
    ax.set_title("Algorithm selected by QBlue (per dataset × error)", fontsize=12)
    ax.legend(fontsize=9, loc="upper right")
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 5: gate reduction box plots
# ---------------------------------------------------------------------------

def plot_gate_reduction(merged: pd.DataFrame, out: Path) -> None:
    merged = merged[merged["phoenix_fair_total"] > 0].copy()
    merged["reduction_pct"] = (
        (merged["phoenix_fair_total"] - merged["qblue_full_total"])
        / merged["phoenix_fair_total"] * 100
    ).clip(lower=-100, upper=100)

    errs_present = sorted(merged["err"].dropna().unique())
    groups = [(ds, err) for ds in DATASET_ORDER for err in errs_present]
    group_labels = [f"{DATASET_LABELS.get(ds,ds)}\n{ERR_LABELS.get(err,err)}"
                    for ds, err in groups]

    data = []
    for ds, err in groups:
        sub = merged[(merged["dataset"] == ds) & (merged["err"] == err)]
        data.append(sub["reduction_pct"].dropna().values)

    fig, ax = plt.subplots(figsize=(max(8, len(groups) * 0.9), 5))
    bp = ax.boxplot(data, patch_artist=True, notch=False,
                    medianprops=dict(color="black", linewidth=1.5))

    for i, (patch, (ds, _)) in enumerate(zip(bp["boxes"], groups)):
        patch.set_facecolor(DATASET_COLORS[ds])
        patch.set_alpha(0.7)

    ax.axhline(0, color="black", linewidth=0.8, linestyle="--")
    ax.set_xticks(range(1, len(groups) + 1))
    ax.set_xticklabels(group_labels, fontsize=7)
    ax.set_ylabel("Total gate reduction  (%)\n(positive = QBlue wins)", fontsize=10)
    ax.set_title("QBlue gate reduction vs. Phoenix×splitting_r", fontsize=12)
    ax.grid(True, axis="y", linestyle=":", linewidth=0.4)
    # legend patches
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor=DATASET_COLORS[ds], alpha=0.7,
                              label=DATASET_LABELS[ds]) for ds in DATASET_ORDER]
    ax.legend(handles=legend_elements, fontsize=9)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", type=Path, default=RESULTS / "plots")
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    print("Loading data...")

    # Best available data: prefer per-t named files, fall back to combined buckets file
    qb = load_qblue(
        RESULTS / "qblue_bucket_s_t_pi4.csv",
        RESULTS / "qblue_bucket_s_t_pi16.csv",
        RESULTS / "qblue_bucket_m_t_pi16.csv",
        RESULTS / "qblue_bucket_l_t_pi16.csv",
        RESULTS / "qblue_buckets.csv",
    )
    ph = load_phoenix(
        RESULTS / "phoenix_bucket_s_t_pi4.csv",
        RESULTS / "phoenix_bucket_s_t_pi16.csv",
        RESULTS / "phoenix_bucket_m_t_pi16.csv",
        RESULTS / "phoenix_bucket_l_t_pi16.csv",
        RESULTS / "phoenix_buckets.csv",
    )
    of = load_phoenix(
        RESULTS / "openfermion_buckets.csv",
    )

    if qb is None:
        print("No QBlue data found — nothing to plot.")
        return

    # Deduplicate: if both per-t file and combined buckets loaded,
    # drop duplicates on (input_name, dataset, t, err, pipeline).
    if qb is not None:
        qb = qb.drop_duplicates(subset=["input_name", "dataset", "t", "err", "pipeline"])
    if ph is not None:
        ph = ph.drop_duplicates(subset=["input_name", "dataset", "t"])

    print(f"  QBlue rows: {len(qb)}")
    print(f"  Phoenix rows: {len(ph) if ph is not None else 0}")
    print(f"  OpenFermion rows: {len(of) if of is not None else 0}")

    print("\nGenerating plots...")

    # Plot 1 & 5: need joined data
    if ph is not None:
        merged = join_qblue_phoenix(qb, ph)
        print(f"  Joined rows: {len(merged)}")
        if len(merged):
            plot_scatter_vs_phoenix(merged, args.out_dir / "fig2_qualitative_gates_vs_phoenix.png")
            plot_gate_reduction(merged, args.out_dir / "tab2_gate_reduction.png")
    else:
        print("  [skip] fig2 & tab2 gate reduction: no Phoenix data")

    # tab2: compile time & gate count — one file per error bound (std pipeline)
    errs_available = sorted(qb["err"].dropna().unique())
    for err in errs_available:
        err_str = str(err).replace(".", "")  # e.g. 0.5 -> "05", 0.02 -> "002"
        qb_err = qb[(qb["err"] == err) & (qb["pipeline"] == "std")]
        plot_compile_time(qb_err, ph, of,
                          args.out_dir / f"tab2_compile_time_err{err_str}.png",
                          err_label=str(err))
        plot_gate_count(qb_err, ph, of,
                        args.out_dir / f"tab2_gate_count_err{err_str}.png",
                        err_label=str(err))

    # fig2: gates vs err — use π/16 data (all three datasets have it)
    T_PI16 = round(0.19634954084936207, 6)
    qb_pi16 = qb[qb["t"].round(6) == T_PI16]
    plot_gates_vs_err(qb_pi16, args.out_dir / "fig2_qualitative_gates_vs_err.png", t_label="t = π/16")

    # tab4: algorithm selection
    plot_algorithm_selection(qb, args.out_dir / "tab4_trotter_select.png")

    print(f"\nDone. Plots saved to {args.out_dir}/")


if __name__ == "__main__":
    main()
