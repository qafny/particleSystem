"""Plot functions from jbg/202603, preserving the original aesthetics."""

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
import pandas as pd
from pathlib import Path

DATASET_ORDER = ["S", "M", "L"]
DATASET_LABELS = {"S": "Small", "M": "Medium", "L": "Large"}
DATASET_COLORS = {"S": "#4C72B0", "M": "#DD8452", "L": "#55A868"}
COMPETITOR_COLORS = {"phoenix": "#C44E52", "openfermion": "#8172B2"}
ERR_ORDER = [0.02, 0.1, 0.5]
ERR_LABELS = {e: f"ε={e}" for e in ERR_ORDER}
T_LABEL_PI16 = "t = π/16"

SIZE_ORDER = ["large", "middle", "small"]
SIZE_LABELS = {"small": "Small", "middle": "Medium", "large": "Large"}
SIZE_COLORS = {"small": DATASET_COLORS["S"], "middle": DATASET_COLORS["M"], "large": DATASET_COLORS["L"], "all": "#333333"}
T_NAMES = {0.7854: "π/4", 0.1963: "π/16"}


def _gate_label(value, _=None):
    for limit, suffix in ((1e12, "T"), (1e9, "B"), (1e6, "M"), (1e3, "K")):
        if value >= limit:
            return f"{value / limit:g}{suffix}"
    return f"{value:g}"


def plot_overall(rows: list[tuple[str, str, pd.DataFrame]], out: Path, title: str, note: str = '') -> None:
    """Total gates per program, QBlue's circuit (purple) over the
    baseline (light purple), one panel per error bound and one row per
    (row label, baseline label, savings rows of one time period). Programs are
    grouped Large | Medium | Small and sorted by the baseline's gate count."""
    errs = sorted(set().union(*(df['error'].unique() for _, _, df in rows)))
    fig, axes = plt.subplots(len(rows), len(errs), figsize=(5.0 * len(errs), 3.4 * len(rows)), sharey=True, squeeze=False)
    peak = max(max(df["ours"].max(), df["theirs"].max()) for _, _, df in rows)
    top = 100 ** np.ceil(np.log(peak * 1.5) / np.log(100))  # next labelled tick (ticks every 100x)
    for row, (row_label, baseline, df) in enumerate(rows):
        for col, err in enumerate(errs):
            ax = axes[row, col]
            sub = df[df['error'] == err].copy()
            sub['order'] = sub['size'].map({s: i for i, s in enumerate(SIZE_ORDER)})
            sub = sub.sort_values(['order', 'theirs'], ascending=[True, False])
            x = np.arange(len(sub))
            theirs, ours = sub['theirs'].clip(lower=1).to_numpy(), sub['ours'].clip(lower=1).to_numpy()
            ax.fill_between(x, 1, theirs, color='#D9C8EE', step='mid', label=baseline)
            ax.plot(x, theirs, color='#B39DDB', linewidth=1.0, drawstyle='steps-mid')
            ax.fill_between(x, 1, ours, color='#6A3D9A', alpha=0.85, step='mid', label='QBlue')
            ax.plot(x, ours, color='#3F1F66', linewidth=1.0, drawstyle='steps-mid')
            start, ticks, names = 0, [], []
            for size in SIZE_ORDER:
                group = sub[sub['size'] == size]
                if group.empty:
                    continue
                end = start + len(group)
                if start:
                    ax.axvline(start - 0.5, color='#444444', linestyle=':', linewidth=0.8)
                ticks.append((start + end - 1) / 2)
                names.append(f"{SIZE_LABELS[size][0] if len(group) < 0.2 * len(sub) else SIZE_LABELS[size]}\n"
                             f"{100 * group['saving'].median():+.0f}%")
                start = end
            ax.set_xlim(-0.5, len(sub) - 0.5)
            ax.set_yscale('log')
            ax.set_ylim(1, top)
            ax.set_xticks(ticks, names, fontsize=8)
            ax.tick_params(axis='x', length=0)
            ax.yaxis.set_major_locator(mticker.LogLocator(base=100))
            ax.yaxis.set_major_formatter(mticker.FuncFormatter(_gate_label))
            ax.yaxis.set_minor_locator(mticker.NullLocator())
            ax.grid(True, axis='y', linestyle=':', linewidth=0.4)
            ax.set_title(f"{row_label}ε = {err:g}   (median {100 * sub['saving'].median():+.0f}%)", fontsize=10)
            if col == 0:
                ax.set_ylabel('Total gates', fontsize=10)
                ax.legend(loc='upper right', fontsize=7.5, frameon=False)
    fig.suptitle(title, fontsize=12)
    fig.text(0.5, 0.005, ('Under each group: median saving of QBlue (L = Large, M = Medium).  ' + note).strip(),
             ha='center', va='bottom', fontsize=8, color='#555555')
    fig.tight_layout(rect=(0, 0.03, 1, 0.97))
    fig.savefig(out, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f'  saved {out.name}')


def plot_summary(df: pd.DataFrame, panels: list[tuple[str, str]], out: Path) -> None:
    """Median saving per size class across the (ε, t) settings, one panel per experiment."""
    settings = sorted({(e, t) for e, t in zip(df['error'], df['time'])}, key=lambda s: (-s[1], s[0]))
    labels = [f"{e:g}\n{T_NAMES.get(round(t, 4), f'{t:g}')}" for e, t in settings]
    cols = 3
    rows = -(-len(panels) // cols)
    fig, axes = plt.subplots(rows, cols, figsize=(4.6 * cols, 3.4 * rows), squeeze=False)
    for ax, (name, title) in zip(axes.flat, panels):
        sub = df[df['experiment'] == name]
        for size in [*SIZE_ORDER, 'all']:
            group = sub if size == 'all' else sub[sub['size'] == size]
            values = [100 * group[(group['error'] == e) & (group['time'] == t)]['saving'].median() for e, t in settings]
            ax.plot(range(len(settings)), values, marker='o', markersize=4, linewidth=1.8 if size == 'all' else 1.4,
                    linestyle='--' if size == 'all' else '-', color=SIZE_COLORS[size],
                    label='All' if size == 'all' else SIZE_LABELS[size])
        ax.axhline(0, color='#777777', linewidth=0.8)
        ax.set_xticks(range(len(settings)))
        ax.set_xticklabels(labels, fontsize=8)
        ax.yaxis.set_major_formatter(mticker.PercentFormatter(decimals=0))
        ax.set_title(title, fontsize=10)
        ax.grid(True, axis='y', linestyle=':', linewidth=0.4)
    for ax in axes.flat[len(panels):]:
        ax.axis('off')
    axes[0, 0].set_ylabel('Median gate saving', fontsize=9)
    handles, names = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, names, loc='lower center', ncol=4, frameon=False, fontsize=9)
    fig.text(0.01, 0.01, 'x-axis: ε, t', fontsize=8, color='#555555')
    fig.tight_layout(rect=(0, 0.05, 1, 1))
    fig.savefig(out, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f'  saved {out.name}')

def plot_compile_time(qb: pd.DataFrame, ph: pd.DataFrame | None, of: pd.DataFrame | None, out: Path, err_label: str='') -> None:
    fig, ax = plt.subplots(figsize=(7, 5))
    ax.scatter(qb['n_terms'], qb['wall_s'], color='#4C72B0', alpha=0.4, s=12, linewidths=0, label='QBlue std')
    if ph is not None:
        ax.scatter(ph['n_terms'], ph['wall_s'], color=COMPETITOR_COLORS['phoenix'], alpha=0.5, s=12, linewidths=0, label='Phoenix')
    if of is not None:
        ax.scatter(of['n_terms'], of['wall_s'], color=COMPETITOR_COLORS['openfermion'], alpha=0.5, s=12, linewidths=0, label='OpenFermion')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlabel('Number of Pauli terms', fontsize=11)
    ax.set_ylabel('Reported compilation time (s)', fontsize=11)
    title = f'Compilation time vs. Hamiltonian size  ({err_label}, {T_LABEL_PI16})' if err_label else 'Compilation time vs. Hamiltonian size'
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which='both', linestyle=':', linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f'  saved {out.name}')

def plot_qdrift_vs_std_polar(qb: pd.DataFrame, out: Path, t_label: str=T_LABEL_PI16) -> None:
    """
    3-panel polar flower plot comparing qdrift vs std pipeline gate counts.
    Each panel is one error bound; each petal is one dataset (S/M/L).
    Outer petal = std median full-circuit gates; inner petal = qdrift median.
    """
    std = qb[qb['pipeline'] == 'std']
    qdrift_df = qb[qb['pipeline'] == 'qdrift']
    if std.empty or qdrift_df.empty:
        print(f'  [skip] polar flower: missing std or qdrift data')
        return
    errs_present = [err for err in ERR_ORDER if err in qb['err'].dropna().unique()]
    datasets = [ds for ds in DATASET_ORDER if ds in qb['dataset'].unique()]
    if not errs_present or not datasets:
        return

    def medians(df):
        return {ds: {err: df[(df['dataset'] == ds) & (df['err'] == err)]['qblue_full_total'].median() for err in errs_present} for ds in datasets}
    std_med = medians(std)
    qdrift_med = medians(qdrift_df)
    all_std = [std_med[ds][err] for ds in datasets for err in errs_present if not np.isnan(std_med[ds][err])]
    if not all_std or max(all_std) <= 0:
        return
    max_log = np.log10(max(all_std))
    PETAL_MAX = 0.88

    def to_r(val: float) -> float:
        if np.isnan(val) or val <= 0:
            return 0.0
        return max(0.0, np.log10(val) / max_log) * PETAL_MAX
    n = len(datasets)
    if n == 1:
        centers_deg = [0]
    elif n == 2:
        centers_deg = [0, 180]
    else:
        centers_deg = [i * (360 / n) for i in range(n)]
    half_width_deg = min(65.0, 180.0 / n - 5)
    n_theta = 300
    fig, axes = plt.subplots(1, len(errs_present), figsize=(5.0 * len(errs_present), 4.5), subplot_kw={'projection': 'polar'})
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])
    for ax, err in zip(axes, errs_present):
        ax.set_theta_zero_location('N')
        ax.set_theta_direction(-1)
        ax.set_rticks([])
        ax.set_xticks([])
        ax.grid(False)
        ax.spines['polar'].set_visible(False)
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
            r_std_arr = r_std * envelope
            r_qdrift_arr = r_qdrift * envelope
            ax.fill(theta, r_std_arr, color=color, alpha=0.2)
            ax.plot(theta, r_std_arr, color=color, linewidth=1.5, linestyle='--', alpha=0.7)
            if r_qdrift > 0:
                ax.fill(theta, r_qdrift_arr, color=color, alpha=0.65)
                ax.plot(theta, r_qdrift_arr, color=color, linewidth=1.8)
            cx = np.sin(center_rad)
            cy = np.cos(center_rad)
            ha = 'left' if cx > 0.25 else 'right' if cx < -0.25 else 'center'
            va = 'bottom' if cy > 0.25 else 'top' if cy < -0.25 else 'center'
            label_r = r_std + 0.18
            q_val = qdrift_med[ds].get(err, np.nan)
            s_val = std_med[ds].get(err, np.nan)
            if r_qdrift > 0 and (not np.isnan(q_val)) and s_val:
                reduction = (1 - q_val / s_val) * 100
                reduction_str = '>99%' if reduction >= 99.5 else f'{reduction:.0f}%'
                label = f'{DATASET_LABELS[ds]}\n{reduction_str} reduction'
            else:
                label = f'{DATASET_LABELS[ds]}\n(no qdrift data)'
            ax.text(center_rad, label_r, label, ha=ha, va=va, fontsize=7.5, color=color, fontweight='bold')
        ax.set_title(ERR_LABELS.get(err, str(err)), fontsize=11, pad=10)
    from matplotlib.lines import Line2D
    legend_handles = [Line2D([0], [0], color='#888888', linewidth=1.5, linestyle='--', label='Trotter (before optimization)'), Line2D([0], [0], color='#888888', linewidth=1.8, linestyle='-', label='QDrift (before optimization)')] + [plt.Rectangle((0, 0), 1, 1, color=DATASET_COLORS[ds], alpha=0.6, label=DATASET_LABELS[ds]) for ds in datasets]
    fig.legend(handles=legend_handles, loc='lower center', bbox_to_anchor=(0.5, 0.0), ncol=len(legend_handles), frameon=False, fontsize=8.5)
    fig.suptitle(f'QDrift vs. Standard Trotterization: gate reduction  ({t_label})', fontsize=12)
    fig.tight_layout(rect=(0, 0.0, 1, 0.95))
    fig.savefig(out, dpi=150, bbox_inches='tight', pad_inches=0.15)
    plt.close(fig)
    print(f'  saved {out.name}')

def plot_analog_vs_digital_polar(merged: pd.DataFrame, ibm_col: str, ind_col: str, gate_label: str, out: Path) -> None:
    """
    Polar flower plot comparing Indiana analog vs IBM digital gate counts.
    Same style as plot_qdrift_vs_std_polar:
      outer petal (dashed) = IBM digital median full-circuit gate count
      inner petal (solid)  = Indiana analog median full-circuit gate count
    One panel per error bound; one petal per dataset.
    Labels show the raw median counts.
    """
    errs_present = [e for e in ERR_ORDER if e in merged['error'].dropna().unique()]
    datasets = [ds for ds in DATASET_ORDER if ds in merged['dataset'].unique()]
    if not errs_present or not datasets:
        print(f'  [skip] {out.name}: no data')
        return

    def med(col, ds, err):
        sub = merged[(merged['dataset'] == ds) & (merged['error'] == err)][col]
        return sub.median() if len(sub) else np.nan
    ibm_med = {ds: {e: med(ibm_col, ds, e) for e in errs_present} for ds in datasets}
    ind_med = {ds: {e: med(ind_col, ds, e) for e in errs_present} for ds in datasets}
    all_ibm = [ibm_med[ds][e] for ds in datasets for e in errs_present if not np.isnan(ibm_med[ds][e])]
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
    fig, axes = plt.subplots(1, len(errs_present), figsize=(5.0 * len(errs_present), 4.5), subplot_kw={'projection': 'polar'})
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])
    for ax, err in zip(axes, errs_present):
        ax.set_theta_zero_location('N')
        ax.set_theta_direction(-1)
        ax.set_rticks([])
        ax.set_xticks([])
        ax.grid(False)
        ax.spines['polar'].set_visible(False)
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
            ax.fill(theta, r_ibm * envelope, color=color, alpha=0.2)
            ax.plot(theta, r_ibm * envelope, color=color, linewidth=1.5, linestyle='--', alpha=0.7)
            if r_ind > 0:
                ax.fill(theta, r_ind * envelope, color=color, alpha=0.65)
                ax.plot(theta, r_ind * envelope, color=color, linewidth=1.8)
            cx = np.sin(center_rad)
            cy = np.cos(center_rad)
            ha = 'left' if cx > 0.25 else 'right' if cx < -0.25 else 'center'
            va = 'bottom' if cy > 0.25 else 'top' if cy < -0.25 else 'center'
            label_r = r_ibm + 0.18
            ibm_val = ibm_med[ds].get(err, np.nan)
            ind_val = ind_med[ds].get(err, np.nan)

            def fmt(v):
                if np.isnan(v) or v <= 0:
                    return '---'
                if v >= 1000000000.0:
                    return f'{v / 1000000000.0:.1f}B'
                if v >= 1000000.0:
                    return f'{v / 1000000.0:.1f}M'
                if v >= 1000.0:
                    return f'{v / 1000.0:.1f}K'
                return f'{v:.0f}'
            label = f'{DATASET_LABELS[ds]}\nIBM: {fmt(ibm_val)}\nInd: {fmt(ind_val)}'
            ax.text(center_rad, label_r, label, ha=ha, va=va, fontsize=7.0, color=color, fontweight='bold')
        ax.set_title(ERR_LABELS.get(err, str(err)), fontsize=11, pad=10)
    from matplotlib.lines import Line2D
    legend_handles = [Line2D([0], [0], color='#888888', linewidth=1.5, linestyle='--', label='IBM digital'), Line2D([0], [0], color='#888888', linewidth=1.8, linestyle='-', label='Indiana analog')] + [plt.Rectangle((0, 0), 1, 1, color=DATASET_COLORS[ds], alpha=0.6, label=DATASET_LABELS[ds]) for ds in datasets]
    fig.legend(handles=legend_handles, loc='lower center', bbox_to_anchor=(0.5, 0.0), ncol=len(legend_handles), frameon=False, fontsize=8.5)
    fig.suptitle(f'Indiana analog vs. IBM digital: {gate_label} gate counts  (full circuit)', fontsize=12)
    fig.tight_layout(rect=(0, 0.08, 1, 0.95))
    fig.savefig(out, dpi=150, bbox_inches='tight', pad_inches=0.15)
    plt.close(fig)
    print(f'  saved {out.name}')
def plot_gate_count(qb: pd.DataFrame, merged_ph: pd.DataFrame | None, merged_of: pd.DataFrame | None, out: Path, err_label: str='') -> None:
    fig, ax = plt.subplots(figsize=(7, 5))
    ax.scatter(qb['n_terms'], qb['qblue_full_total'], color='#4C72B0', alpha=0.4, s=12, linewidths=0, label='QBlue std')
    if merged_ph is not None and (not merged_ph.empty):
        ax.scatter(merged_ph['n_terms'], merged_ph['phoenix_fair_total'], color=COMPETITOR_COLORS['phoenix'], alpha=0.5, s=12, linewidths=0, label='Phoenix × r')
    if merged_of is not None and (not merged_of.empty):
        ax.scatter(merged_of['n_terms'], merged_of['openfermion_fair_total'], color=COMPETITOR_COLORS['openfermion'], alpha=0.5, s=12, linewidths=0, label='OpenFermion × r')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlabel('Number of Pauli terms', fontsize=11)
    ax.set_ylabel('Full-circuit total gates', fontsize=11)
    title = f'Total gates vs. Hamiltonian size  ({err_label}, {T_LABEL_PI16})' if err_label else 'Total gates vs. Hamiltonian size'
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which='both', linestyle=':', linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f'  saved {out.name}')

