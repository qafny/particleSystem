#!/usr/bin/env python3
"""
Generate QBlue bucket comparison plots.

Usage:
    python3 scripts/plot_results.py [--out-dir results/plots]

This script compares QBlue `std` bucket results at `t = pi/16` against the
single-step Phoenix and OpenFermion bucket results. Competitor gate counts are
multiplied by QBlue's `splitting_r` so the comparison is on full-circuit cost.
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
COMPETITOR_COLORS = {"phoenix": "#C44E52", "openfermion": "#8172B2"}

ERR_ORDER = [0.02, 0.1, 0.5]
ERR_LABELS = {0.02: "ε=0.02", 0.1: "ε=0.1", 0.5: "ε=0.5"}

T_PI16 = round(float(np.pi / 16.0), 6)
T_LABEL_PI16 = "t = π/16"

T_PI4 = round(float(np.pi / 4.0), 6)
T_LABEL_PI4 = "t = π/4"


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


def _glob_paths(*patterns: str) -> list[Path]:
    seen: set[Path] = set()
    paths: list[Path] = []
    for pattern in patterns:
        for path in sorted(RESULTS.glob(pattern)):
            if path not in seen:
                seen.add(path)
                paths.append(path)
    return paths


def load_result_0317(path: Path) -> pd.DataFrame | None:
    """
    Load result_0317.csv and reshape it into the same format used by
    plot_qdrift_vs_std_polar (columns: dataset, input_name, err, t,
    pipeline, qblue_full_total).

    Partition by program_size (Pauli string count):
        S  < 100
        M  100 – 1199
        L  ≥ 1200

    Pipeline mapping:
        path_flag == 1  →  std    (full circuit = gates_total × trotter_step)
        path_flag == 3  →  qdrift (trotter_step == 1, so full = gates_total)
    """
    if not path.exists():
        print(f"  [skip] {path.name} not found")
        return None
    print(f"  loading {path.name}")
    df = pd.read_csv(path)
    df = df[df["status"] == "ok"].copy()
    df = df[df["path_flag"].isin([1, 3])].copy()

    df["input_name"] = df["file_name"].str.split("/").str[-1]
    df["err"] = df["error"]
    df["t"] = df["time"].round(6)
    df["gates_total_step"] = df["single_qubit_gates_bfopt"] + df["multi_qubit_gates_bfopt"]
    df["qblue_full_total"] = df["gates_total_step"] * df["trotter_step"]
    df["pipeline"] = df["path_flag"].map({1: "std", 3: "qdrift"})

    def _bucket(n):
        if n < 100:
            return "S"
        elif n < 1200:
            return "M"
        else:
            return "L"
    df["dataset"] = df["program_size"].apply(_bucket)

    cols = ["dataset", "input_name", "err", "t", "pipeline", "qblue_full_total"]
    return df[cols].dropna(subset=["qblue_full_total"])


def load_buckets(*patterns: str) -> pd.DataFrame | None:
    paths = _glob_paths(*patterns)
    if not paths:
        print(f"  [skip] no files matched: {', '.join(patterns)}")
        return None
    for path in paths:
        print(f"  loading {path.name}")
    frames = [_load(p) for p in paths]
    frames = [f for f in frames if f is not None]
    return pd.concat(frames, ignore_index=True) if frames else None


def prepare_qblue(qb: pd.DataFrame, t_val: float = T_PI16) -> pd.DataFrame:
    """Filter to a single t value and compute full-circuit gate columns (all pipelines).

    For std/auto, gates_opt_* are per-step costs and must be multiplied by splitting_r.
    For qdrift, splitting_r is NaN and gates_opt_* are already the full-circuit cost.
    """
    qb = qb[qb["t"].round(6) == t_val].copy()
    qb = qb.drop_duplicates(subset=["input_name", "dataset", "t", "err", "pipeline"])
    r = qb["splitting_r"].fillna(1.0)
    qb["qblue_pre_total"] = qb["gates_in_total"] * r
    qb["qblue_full_CX"]   = qb["gates_opt_CX"]   * r
    qb["qblue_full_total"] = qb["gates_opt_total"] * r
    return qb


def prepare_qblue_std(qb: pd.DataFrame, t_val: float = T_PI16) -> pd.DataFrame:
    return prepare_qblue(qb, t_val=t_val).query("pipeline == 'std'").copy()


def prepare_competitor(df: pd.DataFrame | None, t_val: float = T_PI16) -> pd.DataFrame | None:
    if df is None:
        return None
    df = df[df["t"].round(6) == t_val].copy()
    return df.drop_duplicates(subset=["input_name", "dataset", "t"])


def join_qblue_competitor(qb: pd.DataFrame, other: pd.DataFrame, name: str) -> pd.DataFrame:
    """
    Join QBlue and a single-step competitor on (input_name, dataset, t).
    Result has one row per QBlue row, with competitor columns suffixed by `name`.
    """
    cols = ["input_name", "dataset", "t", "gates_total", "gates_opt_CX", "gates_opt_total", "compile_s", "wall_s", "n_terms"]
    other_key = other[cols].copy()
    other_key = other_key.rename(columns={c: f"{c}_{name}" for c in cols if c not in {"input_name", "dataset", "t"}})
    merged = qb.merge(other_key, on=["input_name", "dataset", "t"], how="inner")
    merged[f"{name}_fair_pre_total"] = merged[f"gates_total_{name}"] * merged["splitting_r"]
    merged[f"{name}_fair_CX"] = merged[f"gates_opt_CX_{name}"] * merged["splitting_r"]
    merged[f"{name}_fair_total"] = merged[f"gates_opt_total_{name}"] * merged["splitting_r"]
    return merged


def _smooth_curve(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    if len(values) < 5:
        return values

    window = max(7, int(len(values) * 0.06))
    if window % 2 == 0:
        window += 1

    log_values = np.log10(np.clip(values, 1.0, None))
    pad = window // 2
    padded = np.pad(log_values, (pad, pad), mode="edge")
    kernel = np.ones(window, dtype=float) / window
    smoothed = np.convolve(padded, kernel, mode="valid")
    return np.power(10.0, smoothed)


def _dense_curve(x: np.ndarray, y: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    if len(x) < 3:
        return x, y

    x_dense = np.linspace(x[0], x[-1], len(x) * 8)
    y_dense = np.interp(x_dense, x, y)
    return x_dense, y_dense


# ---------------------------------------------------------------------------
# Plot 1: scatter QBlue vs competitor×r
# ---------------------------------------------------------------------------

def plot_scatter_vs_competitor(
    merged: pd.DataFrame,
    competitor_key: str,
    competitor_label: str,
    out: Path,
    err_label: str = "",
) -> None:
    xcol = f"{competitor_key}_fair_total"
    if merged.empty or xcol not in merged.columns:
        print(f"  [skip] {out.name}: no joined {competitor_label} rows")
        return

    fig, ax = plt.subplots(figsize=(6, 6))

    for ds in DATASET_ORDER:
        sub = merged[merged["dataset"] == ds]
        if sub.empty:
            continue
        ax.scatter(
            sub[xcol].clip(lower=1),
            sub["qblue_full_total"].clip(lower=1),
            label=DATASET_LABELS[ds],
            color=DATASET_COLORS[ds],
            alpha=0.6, s=18, linewidths=0,
        )

    lims = [1e1, max(merged[xcol].max(), merged["qblue_full_total"].max()) * 2]
    ax.plot(lims, lims, "k--", linewidth=0.8, label="parity")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(lims)
    ax.set_ylim(lims)
    ax.set_xlabel(f"{competitor_label} × r (total gates)", fontsize=11)
    ax.set_ylabel("QBlue std total gates", fontsize=11)
    title = f"QBlue std vs. {competitor_label}  ({err_label}, {T_LABEL_PI16})" if err_label else f"QBlue std vs. {competitor_label}"
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which="both", linestyle=":", linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 2: compilation time vs n_terms
# ---------------------------------------------------------------------------

def plot_compile_time(
    qb: pd.DataFrame,
    ph: pd.DataFrame | None,
    of: pd.DataFrame | None,
    out: Path,
    err_label: str = "",
) -> None:
    fig, ax = plt.subplots(figsize=(7, 5))

    ax.scatter(qb["n_terms"], qb["wall_s"],
               color="#4C72B0", alpha=0.4, s=12, linewidths=0, label="QBlue std")

    if ph is not None:
        ax.scatter(ph["n_terms"], ph["wall_s"],
                   color=COMPETITOR_COLORS["phoenix"], alpha=0.5, s=12, linewidths=0, label="Phoenix")

    if of is not None:
        ax.scatter(of["n_terms"], of["wall_s"],
                   color=COMPETITOR_COLORS["openfermion"], alpha=0.5, s=12, linewidths=0, label="OpenFermion")

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Number of Pauli terms", fontsize=11)
    ax.set_ylabel("Wall time (s)", fontsize=11)
    title = f"Compilation time vs. Hamiltonian size  ({err_label}, {T_LABEL_PI16})" if err_label else "Compilation time vs. Hamiltonian size"
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

def plot_gate_count(
    qb: pd.DataFrame,
    merged_ph: pd.DataFrame | None,
    merged_of: pd.DataFrame | None,
    out: Path,
    err_label: str = "",
) -> None:
    fig, ax = plt.subplots(figsize=(7, 5))

    ax.scatter(qb["n_terms"], qb["qblue_full_total"],
               color="#4C72B0", alpha=0.4, s=12, linewidths=0, label="QBlue std")
    if merged_ph is not None and not merged_ph.empty:
        ax.scatter(merged_ph["n_terms"], merged_ph["phoenix_fair_total"],
                   color=COMPETITOR_COLORS["phoenix"], alpha=0.5, s=12, linewidths=0, label="Phoenix × r")
    if merged_of is not None and not merged_of.empty:
        ax.scatter(merged_of["n_terms"], merged_of["openfermion_fair_total"],
                   color=COMPETITOR_COLORS["openfermion"], alpha=0.5, s=12, linewidths=0, label="OpenFermion × r")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Number of Pauli terms", fontsize=11)
    ax.set_ylabel("Full-circuit total gates", fontsize=11)
    title = f"Total gates vs. Hamiltonian size  ({err_label}, {T_LABEL_PI16})" if err_label else "Total gates vs. Hamiltonian size"
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

    title = f"QBlue std gate count vs. error bound  ({t_label})" if t_label else "QBlue std gate count vs. error bound"
    fig.suptitle(title, fontsize=12)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Plot 4: algorithm selection stacked bar
# ---------------------------------------------------------------------------

def plot_algorithm_selection(qb: pd.DataFrame, out: Path) -> None:
    # Only use `auto` pipeline rows — that's where QBlue freely chose the algorithm
    auto = qb[qb["pipeline"] == "auto"]
    if auto.empty:
        print("  [skip] algorithm_selection: no `auto` pipeline data")
        return

    algos = auto["algorithm"].dropna().unique()
    if len(algos) < 2:
        print(f"  [skip] algorithm_selection: only one algorithm present ({algos})")
        return

    errs_present = sorted(auto["err"].dropna().unique())
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

    # one row per (file, err, t) within auto pipeline
    deduped = auto.drop_duplicates(subset=["input_name", "dataset", "err", "t"])

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

def plot_gate_reduction(
    merged: pd.DataFrame,
    competitor_key: str,
    competitor_label: str,
    out: Path,
    t_label: str = T_LABEL_PI16,
) -> None:
    fair_col = f"{competitor_key}_fair_total"
    fair_pre_col = f"{competitor_key}_fair_pre_total"
    if merged.empty or fair_col not in merged.columns or fair_pre_col not in merged.columns:
        print(f"  [skip] {out.name}: no joined {competitor_label} rows")
        return
    merged = merged[(merged[fair_col] > 0) & (merged["qblue_pre_total"] > 0)].copy()

    errs_present = [err for err in ERR_ORDER if err in merged["err"].dropna().unique()]
    fig, axes = plt.subplots(1, len(errs_present), figsize=(5.2 * len(errs_present), 5), sharey=True)
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])

    qblue_before = "#8DBBFF"
    qblue_after = "#1F5FBF"
    other_after = "#6C3DB8"
    max_gate = 0.0
    plotted = False
    for ax, err in zip(axes, errs_present):
        sub = merged[merged["err"] == err].copy()
        if sub.empty:
            ax.set_title(ERR_LABELS.get(err, str(err)))
            continue

        # Order by QBlue input size descending so hardest examples appear first.
        sub = sub.sort_values(["qblue_pre_total", "dataset", "input_name"], ascending=[False, True, True])

        x = np.arange(1, len(sub) + 1)
        qblue_pre = sub["qblue_pre_total"].to_numpy(dtype=float)
        qblue_post = sub["qblue_full_total"].to_numpy(dtype=float)
        other_post = sub[fair_col].to_numpy(dtype=float)

        qblue_pre_s = _smooth_curve(qblue_pre)
        qblue_post_s = _smooth_curve(qblue_post)
        other_post_s = _smooth_curve(other_post)

        x_qb_pre, y_qb_pre = _dense_curve(x, qblue_pre_s)
        x_qb_post, y_qb_post = _dense_curve(x, qblue_post_s)
        x_other_post, y_other_post = _dense_curve(x, other_post_s)

        ax.plot(x_qb_pre, y_qb_pre, color=qblue_before, linewidth=2.0, linestyle="--", zorder=4)
        ax.fill_between(x_qb_pre, 0, y_qb_pre, color=qblue_before, alpha=0.18, zorder=2)
        ax.plot(x_qb_post, y_qb_post, color=qblue_after, linewidth=2.2, zorder=5)
        ax.fill_between(x_qb_post, 0, y_qb_post, color=qblue_after, alpha=0.14, zorder=3)

        # Competitor: show only final optimized circuit cost (no "before" — their
        # native gate representation is not comparable to standard-basis counts).
        ax.plot(x_other_post, -y_other_post, color=other_after, linewidth=2.2, zorder=5)
        ax.fill_between(x_other_post, 0, -y_other_post, color=other_after, alpha=0.14, zorder=3)

        plotted = True
        max_gate = max(max_gate, qblue_pre.max(), qblue_post.max(), other_post.max())

        ax.axhline(0, color="#777777", linestyle="--", linewidth=1.0, zorder=1)
        ax.set_xlim(1, len(sub))
        tick_positions = sorted(set([1, max(1, len(sub) // 2), len(sub)]))
        ax.set_xticks(tick_positions)
        ax.set_xticklabels([str(t) for t in tick_positions], fontsize=8, color="#555555")
        ax.set_xlabel("Datasets (sorted by circuit size)", fontsize=9, color="#555555")
        ax.set_title(f"{ERR_LABELS.get(err, str(err))}  (n={len(sub)})", fontsize=11)
        ax.grid(True, axis="y", linestyle=":", linewidth=0.4)
        ax.text(0.02, 0.93, "QBlue", transform=ax.transAxes, fontsize=9, color="#444444")
        ax.text(0.02, 0.05, competitor_label, transform=ax.transAxes, fontsize=9, color="#444444")
        if ax is axes[0]:
            ax.set_ylabel("Full-circuit total gates", fontsize=10)

    if not plotted:
        print(f"  [skip] {out.name}: no reduction data")
        plt.close(fig)
        return

    linthresh = max(10.0, min(1e5, max_gate / 1e4))
    ylim = max_gate * 1.08
    for ax in axes:
        ax.set_yscale("symlog", linthresh=linthresh)
        ax.set_ylim(-ylim, ylim)
        ax.yaxis.set_major_formatter(
            mticker.FuncFormatter(
                lambda value, _: (
                    f"{abs(value) / 1e9:.1f}B" if abs(value) >= 1e9 else
                    f"{abs(value) / 1e6:.1f}M" if abs(value) >= 1e6 else
                    f"{abs(value) / 1e3:.1f}K" if abs(value) >= 1e3 else
                    f"{int(abs(value))}"
                )
            )
        )

    title = f"QBlue vs. {competitor_label}: before/after optimization gate counts  ({t_label})"
    fig.suptitle(title, fontsize=12)
    from matplotlib.patches import Patch
    before_median_qb = merged["qblue_pre_total"].median()
    after_median_qb = merged["qblue_full_total"].median()
    after_median_other = merged[fair_col].median()
    legend_handles = [
        Patch(color=qblue_before, label="QBlue before"),
        Patch(color=qblue_after, label="QBlue after"),
        Patch(color=other_after, label=f"{competitor_label} optimized"),
    ]
    fig.legend(
        handles=legend_handles,
        loc="lower center",
        bbox_to_anchor=(0.5, 0.03),
        ncol=3,
        frameon=False,
        fontsize=8.5,
    )
    fig.text(
        0.5,
        0.005,
        (
            f"QBlue medians: before {before_median_qb:,.0f}, after {after_median_qb:,.0f} gates.  "
            f"{competitor_label} median: {after_median_other:,.0f} gates."
        ),
        ha="center",
        va="bottom",
        fontsize=8,
        color="#555555",
    )
    fig.tight_layout(rect=(0, 0.12, 1, 0.95))
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print(f"  saved {out.name}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Plot 6: polar flower — QDrift vs Standard Trotterization gate reduction
# ---------------------------------------------------------------------------

def plot_qdrift_vs_std_polar(qb: pd.DataFrame, out: Path, t_label: str = T_LABEL_PI16) -> None:
    """
    3-panel polar flower plot comparing qdrift vs std pipeline gate counts.
    Each panel is one error bound; each petal is one dataset (S/M/L).
    Outer petal = std median full-circuit gates; inner petal = qdrift median.
    """
    std = qb[qb["pipeline"] == "std"]
    qdrift_df = qb[qb["pipeline"] == "qdrift"]

    if std.empty or qdrift_df.empty:
        print(f"  [skip] polar flower: missing std or qdrift data")
        return

    errs_present = [err for err in ERR_ORDER if err in qb["err"].dropna().unique()]
    datasets = [ds for ds in DATASET_ORDER if ds in qb["dataset"].unique()]
    if not errs_present or not datasets:
        return

    def medians(df):
        return {
            ds: {
                err: df[(df["dataset"] == ds) & (df["err"] == err)]["qblue_full_total"].median()
                for err in errs_present
            }
            for ds in datasets
        }

    std_med = medians(std)
    qdrift_med = medians(qdrift_df)

    # Normalise radii on log scale, globally across all std values so panels are comparable.
    all_std = [std_med[ds][err] for ds in datasets for err in errs_present
               if not np.isnan(std_med[ds][err])]
    if not all_std or max(all_std) <= 0:
        return
    max_log = np.log10(max(all_std))

    PETAL_MAX = 0.88  # petals occupy this fraction of ylim, leaving room for labels

    def to_r(val: float) -> float:
        if np.isnan(val) or val <= 0:
            return 0.0
        return max(0.0, np.log10(val) / max_log) * PETAL_MAX

    # Petal centres: 1-petal top; 2-petal top/bottom; 3+ evenly from top.
    n = len(datasets)
    if n == 1:
        centers_deg = [0]
    elif n == 2:
        centers_deg = [0, 180]
    else:
        centers_deg = [i * (360 / n) for i in range(n)]
    half_width_deg = min(65.0, 180.0 / n - 5)
    n_theta = 300

    fig, axes = plt.subplots(
        1, len(errs_present),
        figsize=(5.0 * len(errs_present), 4.5),
        subplot_kw={"projection": "polar"},
    )
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])

    for ax, err in zip(axes, errs_present):
        ax.set_theta_zero_location("N")
        ax.set_theta_direction(-1)
        ax.set_rticks([])
        ax.set_xticks([])
        ax.grid(False)
        ax.spines["polar"].set_visible(False)
        ax.set_ylim(0, 1.12)

        for ds, center_deg in zip(datasets, centers_deg):
            center_rad = np.deg2rad(center_deg)
            hw_rad = np.deg2rad(half_width_deg)
            color = DATASET_COLORS[ds]

            r_std = to_r(std_med[ds].get(err, np.nan))
            r_qdrift = to_r(qdrift_med[ds].get(err, np.nan))
            if r_std == 0:
                continue

            theta = np.linspace(center_rad - hw_rad, center_rad + hw_rad, n_theta)
            envelope = np.cos((theta - center_rad) / hw_rad * np.pi / 2) ** 2

            r_std_arr    = r_std    * envelope
            r_qdrift_arr = r_qdrift * envelope

            # Outer petal: std (lighter, dashed outline)
            ax.fill(theta, r_std_arr, color=color, alpha=0.20)
            ax.plot(theta, r_std_arr, color=color, linewidth=1.5, linestyle="--", alpha=0.7)

            # Inner petal: qdrift (solid, darker) — only if data exists
            if r_qdrift > 0:
                ax.fill(theta, r_qdrift_arr, color=color, alpha=0.65)
                ax.plot(theta, r_qdrift_arr, color=color, linewidth=1.8)

            # Label just outside the std petal tip, offset in the petal direction.
            # Use Cartesian projection of petal direction to pick ha/va.
            cx = np.sin(center_rad)   # x component (right = positive)
            cy = np.cos(center_rad)   # y component (up = positive)
            ha = "left" if cx > 0.25 else "right" if cx < -0.25 else "center"
            va = "bottom" if cy > 0.25 else "top" if cy < -0.25 else "center"
            label_r = r_std + 0.18

            q_val = qdrift_med[ds].get(err, np.nan)
            s_val = std_med[ds].get(err, np.nan)
            if r_qdrift > 0 and not np.isnan(q_val) and s_val:
                reduction = (1 - q_val / s_val) * 100
                reduction_str = ">99%" if reduction >= 99.5 else f"{reduction:.0f}%"
                label = f"{DATASET_LABELS[ds]}\n{reduction_str} reduction"
            else:
                label = f"{DATASET_LABELS[ds]}\n(no qdrift data)"
            ax.text(
                center_rad, label_r,
                label,
                ha=ha, va=va, fontsize=7.5, color=color, fontweight="bold",
            )

        ax.set_title(ERR_LABELS.get(err, str(err)), fontsize=11, pad=10)

    from matplotlib.lines import Line2D
    legend_handles = [
        Line2D([0], [0], color="#888888", linewidth=1.5, linestyle="--", label="std (before)"),
        Line2D([0], [0], color="#888888", linewidth=1.8, linestyle="-",  label="qdrift (after)"),
    ] + [
        plt.Rectangle((0, 0), 1, 1, color=DATASET_COLORS[ds], alpha=0.6, label=DATASET_LABELS[ds])
        for ds in datasets
    ]
    fig.legend(
        handles=legend_handles,
        loc="lower center",
        bbox_to_anchor=(0.5, 0.0),
        ncol=len(legend_handles),
        frameon=False,
        fontsize=8.5,
    )
    fig.suptitle(
        f"QDrift vs. Standard Trotterization: gate reduction  ({t_label})",
        fontsize=12,
    )
    fig.tight_layout(rect=(0, 0.0, 1, 0.95))
    fig.savefig(out, dpi=150, bbox_inches="tight", pad_inches=0.15)
    plt.close(fig)
    print(f"  saved {out.name}")


def _generate_gate_reduction_plots(
    qb_raw: pd.DataFrame,
    ph_raw: pd.DataFrame | None,
    of_raw: pd.DataFrame | None,
    t_val: float,
    t_label: str,
    t_suffix: str,
    out_dir: Path,
) -> None:
    qb = prepare_qblue_std(qb_raw, t_val=t_val)
    ph = prepare_competitor(ph_raw, t_val=t_val)
    of = prepare_competitor(of_raw, t_val=t_val)

    if len(qb) == 0:
        print(f"  [skip] no QBlue std rows for {t_label}")
        return

    print(f"  QBlue rows ({t_label}): {len(qb)}")
    print(f"  Phoenix rows ({t_label}): {len(ph) if ph is not None else 0}")
    print(f"  OpenFermion rows ({t_label}): {len(of) if of is not None else 0}")

    merged_ph = join_qblue_competitor(qb, ph, "phoenix") if ph is not None else None
    merged_of = join_qblue_competitor(qb, of, "openfermion") if of is not None else None

    if merged_ph is not None and len(merged_ph):
        plot_gate_reduction(
            merged_ph,
            "phoenix",
            "Phoenix",
            out_dir / f"tab2_gate_reduction_phoenix_{t_suffix}.png",
            t_label=t_label,
        )
    if merged_of is not None and len(merged_of):
        plot_gate_reduction(
            merged_of,
            "openfermion",
            "OpenFermion",
            out_dir / f"tab2_gate_reduction_openfermion_{t_suffix}.png",
            t_label=t_label,
        )

    qb_all = prepare_qblue(qb_raw, t_val=t_val)
    plot_qdrift_vs_std_polar(
        qb_all,
        out_dir / f"fig_qdrift_vs_std_polar_{t_suffix}.png",
        t_label=t_label,
    )


def plot_analog_vs_digital_polar(
    merged: pd.DataFrame,
    ibm_col: str,
    ind_col: str,
    gate_label: str,
    out: Path,
) -> None:
    """
    Polar flower plot comparing Indiana analog vs IBM digital gate counts.
    Same style as plot_qdrift_vs_std_polar:
      outer petal (dashed) = IBM digital median full-circuit gate count
      inner petal (solid)  = Indiana analog median full-circuit gate count
    One panel per error bound; one petal per dataset.
    Labels show the raw median counts.
    """
    errs_present = [e for e in ERR_ORDER if e in merged["error"].dropna().unique()]
    datasets = [ds for ds in DATASET_ORDER if ds in merged["dataset"].unique()]
    if not errs_present or not datasets:
        print(f"  [skip] {out.name}: no data")
        return

    def med(col, ds, err):
        sub = merged[(merged["dataset"] == ds) & (merged["error"] == err)][col]
        return sub.median() if len(sub) else np.nan

    ibm_med = {ds: {e: med(ibm_col, ds, e) for e in errs_present} for ds in datasets}
    ind_med = {ds: {e: med(ind_col, ds, e) for e in errs_present} for ds in datasets}

    all_ibm = [ibm_med[ds][e] for ds in datasets for e in errs_present
               if not np.isnan(ibm_med[ds][e])]
    if not all_ibm or max(all_ibm) <= 0:
        return
    max_log = np.log10(max(all_ibm))
    PETAL_MAX = 0.88

    def to_r(val):
        if np.isnan(val) or val <= 0:
            return 0.0
        return max(0.0, np.log10(val) / max_log) * PETAL_MAX

    n = len(datasets)
    centers_deg = [0] if n == 1 else [0, 180] if n == 2 else [i * (360 / n) for i in range(n)]
    half_width_deg = min(65.0, 180.0 / n - 5)
    n_theta = 300

    fig, axes = plt.subplots(
        1, len(errs_present),
        figsize=(5.0 * len(errs_present), 4.5),
        subplot_kw={"projection": "polar"},
    )
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])

    for ax, err in zip(axes, errs_present):
        ax.set_theta_zero_location("N")
        ax.set_theta_direction(-1)
        ax.set_rticks([])
        ax.set_xticks([])
        ax.grid(False)
        ax.spines["polar"].set_visible(False)
        ax.set_ylim(0, 1.12)

        for ds, center_deg in zip(datasets, centers_deg):
            center_rad = np.deg2rad(center_deg)
            hw_rad = np.deg2rad(half_width_deg)
            color = DATASET_COLORS[ds]

            r_ibm = to_r(ibm_med[ds].get(err, np.nan))
            r_ind = to_r(ind_med[ds].get(err, np.nan))
            if r_ibm == 0:
                continue

            theta = np.linspace(center_rad - hw_rad, center_rad + hw_rad, n_theta)
            envelope = np.cos((theta - center_rad) / hw_rad * np.pi / 2) ** 2

            # Outer petal: IBM digital (dashed, lighter)
            ax.fill(theta, r_ibm * envelope, color=color, alpha=0.20)
            ax.plot(theta, r_ibm * envelope, color=color, linewidth=1.5, linestyle="--", alpha=0.7)

            # Inner petal: Indiana analog (solid, darker)
            if r_ind > 0:
                ax.fill(theta, r_ind * envelope, color=color, alpha=0.65)
                ax.plot(theta, r_ind * envelope, color=color, linewidth=1.8)

            cx = np.sin(center_rad)
            cy = np.cos(center_rad)
            ha = "left" if cx > 0.25 else "right" if cx < -0.25 else "center"
            va = "bottom" if cy > 0.25 else "top" if cy < -0.25 else "center"
            label_r = r_ibm + 0.18

            ibm_val = ibm_med[ds].get(err, np.nan)
            ind_val = ind_med[ds].get(err, np.nan)

            def fmt(v):
                if np.isnan(v) or v <= 0:
                    return "---"
                if v >= 1e9:
                    return f"{v/1e9:.1f}B"
                if v >= 1e6:
                    return f"{v/1e6:.1f}M"
                if v >= 1e3:
                    return f"{v/1e3:.1f}K"
                return f"{v:.0f}"

            label = f"{DATASET_LABELS[ds]}\nIBM: {fmt(ibm_val)}\nInd: {fmt(ind_val)}"
            ax.text(center_rad, label_r, label,
                    ha=ha, va=va, fontsize=7.0, color=color, fontweight="bold")

        ax.set_title(ERR_LABELS.get(err, str(err)), fontsize=11, pad=10)

    from matplotlib.lines import Line2D
    legend_handles = [
        Line2D([0], [0], color="#888888", linewidth=1.5, linestyle="--", label="IBM digital"),
        Line2D([0], [0], color="#888888", linewidth=1.8, linestyle="-",  label="Indiana analog"),
    ] + [
        plt.Rectangle((0, 0), 1, 1, color=DATASET_COLORS[ds], alpha=0.6, label=DATASET_LABELS[ds])
        for ds in datasets
    ]
    fig.legend(handles=legend_handles, loc="lower center", bbox_to_anchor=(0.5, 0.0),
               ncol=len(legend_handles), frameon=False, fontsize=8.5)
    fig.suptitle(
        f"Indiana analog vs. IBM digital: {gate_label} gate counts  (full circuit)",
        fontsize=12,
    )
    fig.tight_layout(rect=(0, 0.08, 1, 0.95))
    fig.savefig(out, dpi=150, bbox_inches="tight", pad_inches=0.15)
    plt.close(fig)
    print(f"  saved {out.name}")


def generate_analog_digital_table(path: Path, out_dir: Path) -> None:
    """
    Compute and save a LaTeX table comparing Indiana analog (path_flag=11)
    vs IBM digital (path_flag=1) from result_0317.csv.

    Rows:  1-qubit terms, multi-qubit terms
    Columns: (S, M, L) × (ε=0.02, 0.1, 0.5)
    Values: mean percentage reduction (positive = analog cheaper).

    Multi-qubit cost is adjusted by ×2.5 because a CX gate runs 2.5× faster
    than a multi-qubit analog pulse schedule.
    """
    if not path.exists():
        print(f"  [skip] {path.name} not found — skipping analog/digital table")
        return

    print(f"  generating analog vs. digital table from {path.name}")
    df = pd.read_csv(path)
    df = df[df["status"] == "ok"].copy()

    def _bucket(n):
        if n < 100:
            return "S"
        elif n < 1200:
            return "M"
        else:
            return "L"

    df["dataset"] = df["program_size"].apply(_bucket)
    df["input_name"] = df["file_name"].str.split("/").str[-1]

    ibm = df[df["path_flag"] == 1][
        ["input_name", "dataset", "error", "time", "trotter_step",
         "single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]
    ].copy()
    ind = df[df["path_flag"] == 11][
        ["input_name", "dataset", "error", "time", "trotter_step",
         "single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]
    ].copy()

    ibm = ibm.rename(columns={c: f"ibm_{c}" for c in
                               ["trotter_step", "single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]})
    ind = ind.rename(columns={c: f"ind_{c}" for c in
                               ["trotter_step", "single_qubit_gates_bfopt", "multi_qubit_gates_bfopt"]})

    merged = ibm.merge(ind, on=["input_name", "dataset", "error", "time"])
    if merged.empty:
        print("  [skip] analog/digital table: no matched rows")
        return

    merged["ibm_1q"] = merged["ibm_single_qubit_gates_bfopt"] * merged["ibm_trotter_step"]
    merged["ibm_mq"] = merged["ibm_multi_qubit_gates_bfopt"]  * merged["ibm_trotter_step"]
    merged["ind_1q"] = merged["ind_single_qubit_gates_bfopt"] * merged["ind_trotter_step"]
    merged["ind_mq"] = merged["ind_multi_qubit_gates_bfopt"]  * merged["ind_trotter_step"]

    CX_SPEEDUP = 2.5
    merged["red_1q"] = 1.0 - merged["ind_1q"] / merged["ibm_1q"]
    merged["red_mq"] = 1.0 - (merged["ind_mq"] * CX_SPEEDUP) / merged["ibm_mq"]

    # Polar flower plots
    plot_analog_vs_digital_polar(
        merged, "ibm_1q", "ind_1q", "1-qubit",
        out_dir / "tab_analog_vs_digital_1q_polar.png",
    )
    plot_analog_vs_digital_polar(
        merged, "ibm_mq", "ind_mq", "multi-qubit",
        out_dir / "tab_analog_vs_digital_mq_polar.png",
    )

    def cell(ds, err, col):
        sub = merged[(merged["dataset"] == ds) & (merged["error"] == err)]
        if sub.empty or sub[col].isna().all():
            return "---"
        v = sub[col].mean() * 100
        sign = "+" if v > 0 else ""
        return f"{sign}{v:.0f}\\%"

    rows_1q = [cell(ds, err, "red_1q") for ds in DATASET_ORDER for err in ERR_ORDER]
    rows_mq = [cell(ds, err, "red_mq") for ds in DATASET_ORDER for err in ERR_ORDER]

    def tabrow(label, vals):
        return label + " & " + " & ".join(vals[:3]) + " & " + \
               " & ".join(vals[3:6]) + " & " + " & ".join(vals[6:]) + r" \\"

    lines = [
        r"\begin{table}[t]",
        r"\vspace{-0.5em}",
        r"{\footnotesize",
        r"\begin{tabular}{|l|c|c|c|c|c|c|c|c|c|}",
        r"\hline",
        r"Name & \multicolumn{3}{c|}{Small Set} & \multicolumn{3}{c|}{Medium Set} &  \multicolumn{3}{c|}{Large Set} \\",
        r"\hline",
        r" & $0.02$ & $0.1$ &  $0.5$ & $0.02$ & $0.1$ &  $0.5$ & $0.02$ & $0.1$ &  $0.5$ \\",
        r" \hline",
        tabrow(r"$1$ qubit terms ", rows_1q),
        r"\hline",
        tabrow(r"multi-qubit terms ", rows_mq),
        r" \hline",
        r"\end{tabular}",
        r"}",
        r"\caption{The average reduction of terms, comparing the Indiana analog vs.\ IBM digital. "
        r"$1$/multi qubit terms refer to $1$/$2$ qubit gates in the digital and $1$/multi qubit "
        r"pulse schedules in the analog systems, respectively. The result takes into account that "
        r"a $2$ qubit \cn{CX} gate runs $2.5$ times faster than a multi-qubit analog pulse schedule.}",
        r"\label{tab:analog-selecta}",
        r"\end{table}",
    ]

    tex = "\n".join(lines)
    out_path = out_dir / "tab_analog_vs_digital.tex"
    out_path.write_text(tex)
    print(f"  saved {out_path.name}")
    print()
    print(tex)
    print()

    # --- matplotlib figure ---
    errs = ERR_ORDER
    datasets = DATASET_ORDER
    n_groups = len(datasets) * len(errs)
    x = np.arange(n_groups)
    width = 0.35

    vals_1q = np.array([
        merged[(merged["dataset"] == ds) & (merged["error"] == err)]["red_1q"].mean() * 100
        for ds in datasets for err in errs
    ])
    vals_mq = np.array([
        merged[(merged["dataset"] == ds) & (merged["error"] == err)]["red_mq"].mean() * 100
        for ds in datasets for err in errs
    ])

    fig, ax = plt.subplots(figsize=(10, 4.5))
    ax.bar(x - width / 2, vals_1q, width, label="1-qubit terms", color="#4C72B0", alpha=0.85)
    ax.bar(x + width / 2, vals_mq, width, label="multi-qubit terms", color="#DD8452", alpha=0.85)

    ax.axhline(0, color="black", linewidth=0.8)
    ax.set_xticks(x)
    group_labels = [
        f"{DATASET_LABELS[ds]}\nε={err}"
        for ds in datasets for err in errs
    ]
    ax.set_xticklabels(group_labels, fontsize=8)
    ax.set_ylabel("Average reduction (%)", fontsize=10)
    ax.set_title(
        "Indiana analog vs. IBM digital: average term reduction\n"
        "(multi-qubit adjusted for 2.5× CX speedup)",
        fontsize=11,
    )
    ax.legend(fontsize=9)
    ax.grid(True, axis="y", linestyle=":", linewidth=0.4)
    fig.tight_layout()

    fig_path = out_dir / "tab_analog_vs_digital.png"
    fig.savefig(fig_path, dpi=150)
    plt.close(fig)
    print(f"  saved {fig_path.name}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", type=Path, default=RESULTS / "plots")
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    print("Loading data...")

    qb_raw = load_buckets(
        "qblue_bucket_*_t_pi16.csv", "qblue_buckets_*_t_pi16.csv",
        "qblue_bucket_*_t_pi4.csv",  "qblue_buckets_*_t_pi4.csv",
    )
    ph_raw = load_buckets(
        "phoenix_bucket_*_t_pi16.csv", "phoenix_buckets_*_t_pi16.csv",
        "phoenix_bucket_*_t_pi4.csv",  "phoenix_buckets_*_t_pi4.csv",
    )
    of_raw = load_buckets(
        "openfermion_bucket_*_t_pi16.csv", "openfermion_buckets_*_t_pi16.csv",
        "openfermion_bucket_*_t_pi4.csv",  "openfermion_buckets_*_t_pi4.csv",
    )

    if qb_raw is None:
        print("No QBlue data found — nothing to plot.")
        return

    # --- pi/16 plots ---
    print("\n=== t = π/16 ===")
    qb16 = prepare_qblue_std(qb_raw, t_val=T_PI16)
    ph16 = prepare_competitor(ph_raw, t_val=T_PI16)
    of16 = prepare_competitor(of_raw, t_val=T_PI16)

    print(f"  QBlue rows: {len(qb16)}")
    print(f"  Phoenix rows: {len(ph16) if ph16 is not None else 0}")
    print(f"  OpenFermion rows: {len(of16) if of16 is not None else 0}")

    merged_ph16_all = join_qblue_competitor(qb16, ph16, "phoenix") if ph16 is not None else None
    merged_of16_all = join_qblue_competitor(qb16, of16, "openfermion") if of16 is not None else None

    errs_available = sorted(qb16["err"].dropna().unique())
    for err in errs_available:
        err_str = str(err).replace(".", "")
        qb_err = qb16[qb16["err"] == err].copy()
        merged_ph = join_qblue_competitor(qb_err, ph16, "phoenix") if ph16 is not None else None
        merged_of = join_qblue_competitor(qb_err, of16, "openfermion") if of16 is not None else None

        plot_compile_time(qb_err, ph16, of16,
                          args.out_dir / f"tab2_compile_time_err{err_str}_pi16.png",
                          err_label=str(err))
        plot_gate_count(qb_err, merged_ph, merged_of,
                        args.out_dir / f"tab2_gate_count_err{err_str}_pi16.png",
                        err_label=str(err))
        if merged_ph is not None and len(merged_ph):
            plot_scatter_vs_competitor(
                merged_ph, "phoenix", "Phoenix",
                args.out_dir / f"fig2_scatter_qblue_vs_phoenix_err{err_str}_pi16.png",
                err_label=str(err),
            )
        if merged_of is not None and len(merged_of):
            plot_scatter_vs_competitor(
                merged_of, "openfermion", "OpenFermion",
                args.out_dir / f"fig2_scatter_qblue_vs_openfermion_err{err_str}_pi16.png",
                err_label=str(err),
            )

    plot_gates_vs_err(qb16, args.out_dir / "fig2_qualitative_gates_vs_err_pi16.png", t_label=T_LABEL_PI16)

    qb16_all = prepare_qblue(qb_raw, t_val=T_PI16)
    plot_qdrift_vs_std_polar(
        qb16_all,
        args.out_dir / "fig_qdrift_vs_std_polar_pi16.png",
        t_label=T_LABEL_PI16,
    )

    if merged_ph16_all is not None and len(merged_ph16_all):
        plot_gate_reduction(
            merged_ph16_all, "phoenix", "Phoenix",
            args.out_dir / "tab2_gate_reduction_phoenix_pi16.png",
            t_label=T_LABEL_PI16,
        )
    if merged_of16_all is not None and len(merged_of16_all):
        plot_gate_reduction(
            merged_of16_all, "openfermion", "OpenFermion",
            args.out_dir / "tab2_gate_reduction_openfermion_pi16.png",
            t_label=T_LABEL_PI16,
        )

    # --- result_0317 polar plots + analog vs digital table ---
    print("\n=== result_0317 polar plots ===")
    r0317 = load_result_0317(RESULTS / "result_0317.csv")
    generate_analog_digital_table(RESULTS / "result_0317.csv", args.out_dir)
    if r0317 is not None:
        for t_val, t_label, t_suffix in [
            (T_PI16, T_LABEL_PI16, "pi16"),
            (T_PI4,  T_LABEL_PI4,  "pi4"),
        ]:
            sub = r0317[r0317["t"] == t_val]
            if not sub.empty:
                plot_qdrift_vs_std_polar(
                    sub,
                    args.out_dir / f"fig_qdrift_vs_std_polar_result0317_{t_suffix}.png",
                    t_label=t_label,
                )

    # --- pi/4 plots ---
    print("\n=== t = π/4 ===")
    _generate_gate_reduction_plots(
        qb_raw, ph_raw, of_raw,
        t_val=T_PI4, t_label=T_LABEL_PI4, t_suffix="pi4",
        out_dir=args.out_dir,
    )

    print(f"\nDone. Plots saved to {args.out_dir}/")


if __name__ == "__main__":
    main()
