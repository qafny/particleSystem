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

def _smooth_curve(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    if len(values) < 5:
        return values
    window = max(7, int(len(values) * 0.06))
    if window % 2 == 0:
        window += 1
    log_values = np.log10(np.clip(values, 1.0, None))
    pad = window // 2
    padded = np.pad(log_values, (pad, pad), mode='edge')
    kernel = np.ones(window, dtype=float) / window
    smoothed = np.convolve(padded, kernel, mode='valid')
    return np.power(10.0, smoothed)

def _dense_curve(x: np.ndarray, y: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    if len(x) < 3:
        return (x, y)
    x_dense = np.linspace(x[0], x[-1], len(x) * 8)
    y_dense = np.interp(x_dense, x, y)
    return (x_dense, y_dense)

def plot_scatter_vs_competitor(merged: pd.DataFrame, competitor_key: str, competitor_label: str, out: Path, err_label: str='') -> None:
    xcol = f'{competitor_key}_fair_total'
    if merged.empty or xcol not in merged.columns:
        print(f'  [skip] {out.name}: no joined {competitor_label} rows')
        return
    fig, ax = plt.subplots(figsize=(6, 6))
    for ds in DATASET_ORDER:
        sub = merged[merged['dataset'] == ds]
        if sub.empty:
            continue
        ax.scatter(sub[xcol].clip(lower=1), sub['qblue_full_total'].clip(lower=1), label=DATASET_LABELS[ds], color=DATASET_COLORS[ds], alpha=0.6, s=18, linewidths=0)
    lims = [10.0, max(merged[xcol].max(), merged['qblue_full_total'].max()) * 2]
    ax.plot(lims, lims, 'k--', linewidth=0.8, label='parity')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(lims)
    ax.set_ylim(lims)
    ax.set_xlabel(f'{competitor_label} × r (total gates)', fontsize=11)
    ax.set_ylabel('QBlue std total gates', fontsize=11)
    title = f'QBlue std vs. {competitor_label}  ({err_label}, {T_LABEL_PI16})' if err_label else f'QBlue std vs. {competitor_label}'
    ax.set_title(title, fontsize=12)
    ax.legend(fontsize=9)
    ax.grid(True, which='both', linestyle=':', linewidth=0.4)
    fig.tight_layout()
    fig.savefig(out, dpi=150, bbox_inches="tight")
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight")
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
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight")
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
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight")
    plt.close(fig)
    print(f'  saved {out.name}')

def plot_gate_reduction(merged: pd.DataFrame, competitor_key: str, competitor_label: str, out: Path, t_label: str=T_LABEL_PI16) -> None:
    fair_col = f'{competitor_key}_fair_total'
    fair_pre_col = f'{competitor_key}_fair_pre_total'
    if merged.empty or fair_col not in merged.columns or fair_pre_col not in merged.columns:
        print(f'  [skip] {out.name}: no joined {competitor_label} rows')
        return
    merged = merged[(merged[fair_col] > 0) & (merged['qblue_pre_total'] > 0)].copy()
    errs_present = [err for err in ERR_ORDER if err in merged['err'].dropna().unique()]
    fig, axes = plt.subplots(1, len(errs_present), figsize=(5.2 * len(errs_present), 5), sharey=True)
    if not isinstance(axes, np.ndarray):
        axes = np.array([axes])
    qblue_before = '#8DBBFF'
    qblue_after = '#1F5FBF'
    other_after = '#6C3DB8'
    max_gate = 0.0
    plotted = False
    for ax, err in zip(axes, errs_present):
        sub = merged[merged['err'] == err].copy()
        if sub.empty:
            ax.set_title(ERR_LABELS.get(err, str(err)))
            continue
        sub = sub.sort_values(['qblue_pre_total', 'dataset', 'input_name'], ascending=[False, True, True])
        x = np.arange(1, len(sub) + 1)
        qblue_pre = sub['qblue_pre_total'].to_numpy(dtype=float)
        qblue_post = sub['qblue_full_total'].to_numpy(dtype=float)
        other_post = sub[fair_col].to_numpy(dtype=float)
        qblue_pre_s = _smooth_curve(qblue_pre)
        qblue_post_s = _smooth_curve(qblue_post)
        other_post_s = _smooth_curve(other_post)
        x_qb_pre, y_qb_pre = _dense_curve(x, qblue_pre_s)
        x_qb_post, y_qb_post = _dense_curve(x, qblue_post_s)
        x_other_post, y_other_post = _dense_curve(x, other_post_s)
        ax.plot(x_qb_pre, y_qb_pre, color=qblue_before, linewidth=2.0, linestyle='--', marker='o' if len(sub) == 1 else None, zorder=4)
        ax.fill_between(x_qb_pre, 0, y_qb_pre, color=qblue_before, alpha=0.18, zorder=2)
        ax.plot(x_qb_post, y_qb_post, color=qblue_after, linewidth=2.2, marker='o' if len(sub) == 1 else None, zorder=5)
        ax.fill_between(x_qb_post, 0, y_qb_post, color=qblue_after, alpha=0.14, zorder=3)
        ax.plot(x_other_post, -y_other_post, color=other_after, linewidth=2.2, marker='o' if len(sub) == 1 else None, zorder=5)
        ax.fill_between(x_other_post, 0, -y_other_post, color=other_after, alpha=0.14, zorder=3)
        plotted = True
        max_gate = max(max_gate, qblue_pre.max(), qblue_post.max(), other_post.max())
        ax.axhline(0, color='#777777', linestyle='--', linewidth=1.0, zorder=1)
        ax.set_xlim((0.5, 1.5) if len(sub) == 1 else (1, len(sub)))
        tick_positions = sorted(set([1, max(1, len(sub) // 2), len(sub)]))
        ax.set_xticks(tick_positions)
        ax.set_xticklabels([str(t) for t in tick_positions], fontsize=8, color='#555555')
        ax.set_xlabel('Datasets (sorted by circuit size)', fontsize=9, color='#555555')
        ax.set_title(f'{ERR_LABELS.get(err, str(err))}  (n={len(sub)})', fontsize=11)
        ax.grid(True, axis='y', linestyle=':', linewidth=0.4)
        ax.text(0.02, 0.93, 'QBlue', transform=ax.transAxes, fontsize=9, color='#444444')
        ax.text(0.02, 0.05, competitor_label, transform=ax.transAxes, fontsize=9, color='#444444')
        if ax is axes[0]:
            ax.set_ylabel('Full-circuit total gates', fontsize=10)
    if not plotted:
        print(f'  [skip] {out.name}: no reduction data')
        plt.close(fig)
        return
    linthresh = max(10.0, min(100000.0, max_gate / 10000.0))
    ylim = max_gate * 1.08
    for ax in axes:
        ax.set_yscale('symlog', linthresh=linthresh)
        ax.set_ylim(-ylim, ylim)
        ax.yaxis.set_major_formatter(mticker.FuncFormatter(lambda value, _: f'{abs(value) / 1000000000.0:.1f}B' if abs(value) >= 1000000000.0 else f'{abs(value) / 1000000.0:.1f}M' if abs(value) >= 1000000.0 else f'{abs(value) / 1000.0:.1f}K' if abs(value) >= 1000.0 else f'{int(abs(value))}'))
    title = f'QBlue vs. {competitor_label}: before/after optimization gate counts  ({t_label})'
    fig.suptitle(title, fontsize=12)
    from matplotlib.patches import Patch
    before_median_qb = merged['qblue_pre_total'].median()
    after_median_qb = merged['qblue_full_total'].median()
    after_median_other = merged[fair_col].median()
    legend_handles = [Patch(color=qblue_before, label='QBlue before'), Patch(color=qblue_after, label='QBlue after'), Patch(color=other_after, label=f'{competitor_label} optimized')]
    fig.legend(handles=legend_handles, loc='lower center', bbox_to_anchor=(0.5, 0.03), ncol=3, frameon=False, fontsize=8.5)
    fig.text(0.5, 0.005, f'QBlue medians: before {before_median_qb:,.0f}, after {after_median_qb:,.0f} gates.  {competitor_label} median: {after_median_other:,.0f} gates.', ha='center', va='bottom', fontsize=8, color='#555555')
    fig.tight_layout(rect=(0, 0.12, 1, 0.95))
    fig.savefig(out, dpi=150, bbox_inches="tight")
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight")
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
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight", pad_inches=0.15)
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
    fig.savefig(out.with_suffix(".pdf"), bbox_inches="tight", pad_inches=0.15)
    fig.savefig(out, dpi=150, bbox_inches='tight', pad_inches=0.15)
    plt.close(fig)
    print(f'  saved {out.name}')
