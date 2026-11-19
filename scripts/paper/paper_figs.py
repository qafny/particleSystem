"""Tables and figures for the paper's evaluation (RQ2, RQ3) and discussion (BE vs Trotter,
BE algorithms, BE vs the Indiana analog machine).

Reads results/qblue_results.csv, lcu_results.csv, grid_extra.csv (overrides the
others), pennylane_lcu*.csv and pennylane_angle_stats*.csv; writes
results/paper/*.tex, *.png/pdf and summary.md. Run with `make paper`.
"""
import csv
import statistics as st
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
import pandas as pd
from plot_style import SIZE_COLORS, SIZE_LABELS, SIZE_ORDER, plot_overall

R = ROOT / "results"
OUT = R / "paper"
OUT.mkdir(exist_ok=True)
TROTTER = {1: "Trotter-1", 2: "Trotter-2", 3: "QDrift", 6: "MarQSim (CNOT)", 7: "MarQSim (CNOT+1q)"}
BE = {8: "QSVT", 9: "QSP", 30: "Taylor", 31: "Quantum walk"}
INDIANA = {11: "Trotter-1", 12: "Trotter-2", 13: "QDrift", 16: "MarQSim"}
TIMES = [0.1963, 0.7854, 3.1416, 12.5664]
TNAME = {0.1963: r"\pi/16", 0.7854: r"\pi/4", 3.1416: r"\pi", 12.5664: r"4\pi"}
TPLAIN = {0.1963: "π/16", 0.7854: "π/4", 3.1416: "π", 12.5664: "4π"}
EPS = [0.1, 0.02, 0.002, 0.0002]
SIZES = ["small", "middle", "large"]
SNAME = {"small": "Small", "middle": "Medium", "large": "Large"}


def size(f):
    return next((s for s in SIZES if f"/{s}/" in f), "other")


def load(name, key_path=True):
    p = R / name
    if not p.exists():
        return {}
    out = {}
    for r in csv.DictReader(open(p, newline="")):
        if r.get("status", "ok") != "ok":
            continue
        k = (r["file_name"], int(r["path_flag"]) if key_path else r["method"],
             float(r["error"]), round(float(r["time"]), 4))
        out[k] = r
    return out


q = {}
for name in ("qblue_results.csv", "lcu_results.csv", "grid_extra.csv"):
    q.update(load(name))
files = sorted({k[0] for k in q})
tot = lambda r: float(r["single_qubit_gates"]) + float(r["multi_qubit_gates"])
nq_of = {k[0]: int(r["nqubit"]) for k, r in q.items()}


def qubits(r, p):
    return int(r["compilation_terms"]) if p in BE else int(r["nqubit"])


def best(f, e, t, paths):
    c = {p: q[(f, p, e, t)] for p in paths if (f, p, e, t) in q}
    if not c:
        return None
    p = min(c, key=lambda p: tot(c[p]))
    return p, c[p]


def red(ours, theirs):
    """reduction of the side that uses fewer: >0 when ours is smaller"""
    return 1 - ours / theirs if ours <= theirs else -(1 - theirs / ours)


def pct(x):
    return f"{100 * x:.0f}\\%" if x is not None else "--"


def med(v):
    return st.median(v) if v else None


md = ["# Paper tables and figures\n", f"{len(files)} programs. Ratios and reductions are medians over programs.\n"]

# ---------------------------------------------------------------- 5.0.1 best BE vs best Trotter
tex = [r"% 5.0.1 best BE vs best Trotter (generated)", r"\begin{tabular}{llrrrrrrrrr}", r"\toprule",
       r" & & \multicolumn{3}{c}{BE wins (programs)} & \multicolumn{3}{c}{Gate reduction of Trotter} & "
       r"\multicolumn{3}{c}{Qubits, BE / Trotter} \\",
       r"\cmidrule(lr){3-5}\cmidrule(lr){6-8}\cmidrule(lr){9-11}",
       r"$t$ & $\epsilon$ & S & M & L & S & M & L & S & M & L \\", r"\midrule"]
md += ["## 5.0.1 Best BE vs best Trotter\n",
       "Gate reduction > 0: the best Trotter-family circuit has fewer gates. BE wins = programs where the best BE "
       "circuit has fewer gates.\n",
       "| t | ε | BE wins S/M/L | gate red. S | M | L | qubits BE/Trotter S | M | L | best Trotter | best BE |",
       "|---|---|---|---|---|---|---|---|---|---|---|"]
rows501 = []
for t in TIMES:
    for e in EPS:
        wins, gr, qr, bt, bb = {}, {}, {}, Counter(), Counter()
        for s in SIZES:
            w = n = 0
            g, qq = [], []
            for f in files:
                if size(f) != s:
                    continue
                a, b = best(f, e, t, TROTTER), best(f, e, t, BE)
                if not a or not b:
                    continue
                n += 1
                w += tot(b[1]) < tot(a[1])
                g.append(red(tot(a[1]), tot(b[1])))
                qq.append(qubits(b[1], b[0]) / qubits(a[1], a[0]))
                bt[TROTTER[a[0]]] += 1
                bb[BE[b[0]]] += 1
                rows501.append(dict(file_name=f, size=s, time=t, error=e, trotter=TROTTER[a[0]], trotter_gates=tot(a[1]),
                                    trotter_qubits=qubits(a[1], a[0]), be=BE[b[0]], be_gates=tot(b[1]),
                                    be_qubits=qubits(b[1], b[0])))
            wins[s], gr[s], qr[s] = (w, n), med(g), med(qq)
        if not any(n for _, n in wins.values()):
            continue
        tex.append(f"${TNAME[t]}$ & {e:g} & " + " & ".join(f"{w}/{n}" for w, n in wins.values()) + " & "
                   + " & ".join(pct(gr[s]) for s in SIZES) + " & "
                   + " & ".join(f"{qr[s]:.1f}$\\times$" if qr[s] else "--" for s in SIZES) + r" \\")
        md.append(f"| {TPLAIN[t]} | {e:g} | " + " / ".join(f"{w}/{n}" for w, n in wins.values()) + " | "
                  + " | ".join(pct(gr[s]).replace("\\", "") for s in SIZES) + " | "
                  + " | ".join(f"{qr[s]:.1f}×" if qr[s] else "–" for s in SIZES) + " | "
                  + ", ".join(f"{k} ({v})" for k, v in bt.most_common(2)) + " | "
                  + ", ".join(f"{k} ({v})" for k, v in bb.most_common(2)) + " |")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_be_vs_trotter.tex").write_text("\n".join(tex), encoding="utf-8")
pd.DataFrame(rows501).to_csv(OUT / "be_vs_trotter.csv", index=False)
md.append("")

# figure: share of programs where BE wins, per t x eps, one line per size
fig, axes = plt.subplots(3, 4, figsize=(13, 8), sharey="row", sharex=True)
df = pd.DataFrame(rows501)
if len(df):
    df["be_win"] = df.be_gates < df.trotter_gates
    df["ratio"] = df.be_gates / df.trotter_gates
    df["qratio"] = df.be_qubits / df.trotter_qubits
    for j, t in enumerate(TIMES):
        for row, col in ((0, "be_win"), (1, "ratio"), (2, "qratio")):
            ax = axes[row, j]
            for s in SIZES:
                sub = df[(df["size"] == s) & (df.time == t)]
                y = [sub[sub.error == e][col].mean() if col == "be_win" else sub[sub.error == e][col].median()
                     for e in EPS]
                ax.plot([str(e) for e in EPS], y, marker="o", markersize=4, linewidth=1.6, color=SIZE_COLORS[s],
                        label=f"{SNAME[s]} ({sub.file_name.nunique()})")
            ax.grid(True, linestyle=":", linewidth=0.4)
            if row == 1:
                ax.axhline(1, color="#333", linewidth=0.8)
            if row == 2:
                ax.set_xlabel("ε")
        axes[0, j].set_title(f"t = {TPLAIN[t]}", fontsize=10)
    axes[0, 0].set_ylabel("Programs where best BE\nuses fewer gates", fontsize=9)
    axes[1, 0].set_ylabel("Median gates,\nbest BE / best Trotter", fontsize=9)
    axes[2, 0].set_ylabel("Median qubits,\nbest BE / best Trotter", fontsize=9)
    axes[2, 0].set_ylim(1, 3.5)
    axes[2, 0].yaxis.set_major_formatter(mticker.FuncFormatter(lambda v, _: f"{v:g}×"))
    axes[0, 0].yaxis.set_major_formatter(mticker.PercentFormatter(1.0))
    axes[0, 0].set_ylim(-0.04, 1.04)
    axes[1, 0].set_yscale("log")
    axes[1, 0].yaxis.set_major_formatter(mticker.FuncFormatter(lambda v, _: f"{v:g}×"))
    axes[0, 0].legend(fontsize=8, frameon=False, loc="upper left")
    fig.tight_layout()
    fig.savefig(OUT / "fig_be_vs_trotter.png", dpi=200, bbox_inches="tight")
    fig.savefig(OUT / "fig_be_vs_trotter.pdf", bbox_inches="tight")
plt.close(fig)

# ---------------------------------------------------------------- 5.0.2 BE algorithms against each other
tex = [r"% 5.0.2 BE algorithms (generated)", r"\begin{tabular}{lll" + "r" * 8 + "}", r"\toprule",
       r" & & & \multicolumn{4}{c}{Cheapest (programs)} & \multicolumn{4}{c}{Gates / best BE (median)} \\",
       r"\cmidrule(lr){4-7}\cmidrule(lr){8-11}",
       r"$t$ & $\epsilon$ & Set & " + " & ".join(BE.values()) + " & " + " & ".join(BE.values()) + r" \\",
       r"\midrule"]
md += ["## 5.0.2 BE algorithms\n", "Cheapest = programs where that method has the fewest gates; ratio = its gates over "
       "the cheapest BE method's (1× when it is the cheapest).\n",
       "| t | ε | set | " + " | ".join(f"cheapest {v}" for v in BE.values()) + " | "
       + " | ".join(f"{v} / best" for v in BE.values()) + " | qubits " + " / ".join(BE.values()) + " |",
       "|---" * (3 + 2 * len(BE) + 1) + "|"]
for t in TIMES:
    for e in EPS:
        for s in SIZES:
            c, ratios, qb = Counter(), defaultdict(list), defaultdict(list)
            for f in files:
                if size(f) != s or not all((f, p, e, t) in q for p in BE):
                    continue
                g = {p: tot(q[(f, p, e, t)]) for p in BE}
                b = min(g, key=g.get)
                c[b] += 1
                for p in BE:
                    ratios[p].append(g[p] / g[b])
                    qb[p].append(int(q[(f, p, e, t)]["compilation_terms"]))
            if not ratios:
                continue
            tex.append(f"${TNAME[t]}$ & {e:g} & {SNAME[s]} & " + " & ".join(str(c[p]) for p in BE) + " & "
                       + " & ".join(f"{med(ratios[p]):.2f}" for p in BE) + r" \\")
            md.append(f"| {TPLAIN[t]} | {e:g} | {SNAME[s]} | " + " | ".join(str(c[p]) for p in BE) + " | "
                      + " | ".join(f"{med(ratios[p]):.2f}×" for p in BE) + " | "
                      + " / ".join(f"{med(qb[p]):.0f}" for p in BE) + " |")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_be_algorithms.tex").write_text("\n".join(tex), encoding="utf-8")
md.append("")

# ---------------------------------------------------------------- 5.0.3 best BE (digital) vs best Indiana analog Trotter
tex = [r"% 5.0.3 best BE (IBM digital) vs best Trotter on Indiana analog (generated)",
       r"\begin{tabular}{ll" + "r" * 6 + "}", r"\toprule",
       r" & & \multicolumn{3}{c}{1-qubit reduction (analog)} & \multicolumn{3}{c}{Multi-qubit reduction (analog)} \\",
       r"\cmidrule(lr){3-5}\cmidrule(lr){6-8}",
       r"$t$ & $\epsilon$ & S & M & L & S & M & L \\", r"\midrule"]
md += ["## 5.0.3 Best BE (digital) vs best Trotter on the Indiana analog machine\n",
       "Reduction > 0: the analog schedule has fewer terms than the best BE circuit has gates. 1-qubit = 1-qubit "
       "gates vs 1-qubit pulses; multi-qubit = CX vs multi-qubit pulses. Best analog = the Indiana path with the "
       "fewest multi-qubit pulses.\n",
       "| t | ε | 1q S | M | L | multi S | M | L | n S/M/L |", "|---|---|---|---|---|---|---|---|---|"]
for t in TIMES:
    for e in EPS:
        one, multi, ns = {}, {}, {}
        for s in SIZES:
            o, m = [], []
            for f in files:
                if size(f) != s:
                    continue
                b = best(f, e, t, BE)
                a = {p: q[(f, p, e, t)] for p in INDIANA if (f, p, e, t) in q}
                if not b or not a:
                    continue
                pa = min(a, key=lambda p: float(a[p]["multi_qubit_gates"]))
                ra = a[pa]
                o.append(red(float(ra["single_qubit_gates"]), float(b[1]["single_qubit_gates"])))
                m.append(red(float(ra["multi_qubit_gates"]), float(b[1]["multi_qubit_gates"])))
            one[s], multi[s], ns[s] = med(o), med(m), len(o)
        if not any(ns.values()):
            continue
        tex.append(f"${TNAME[t]}$ & {e:g} & " + " & ".join(pct(one[s]) for s in SIZES) + " & "
                   + " & ".join(pct(multi[s]) for s in SIZES) + r" \\")
        md.append(f"| {TPLAIN[t]} | {e:g} | " + " | ".join(pct(one[s]).replace("\\", "") for s in SIZES) + " | "
                  + " | ".join(pct(multi[s]).replace("\\", "") for s in SIZES) + " | "
                  + "/".join(str(ns[s]) for s in SIZES) + " |")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_be_vs_analog.tex").write_text("\n".join(tex), encoding="utf-8")
md.append("")

# figure for 5.0.3: like the old analog-vs-digital bars, one panel per t, bars per (size, eps)
fig, axes = plt.subplots(2, 2, figsize=(12, 7), sharey=True)
axes = axes.ravel()
for ax, t in zip(axes, TIMES):
    labels, one_v, multi_v = [], [], []
    for s in SIZES:
        for e in EPS:
            o, m = [], []
            for f in files:
                if size(f) != s:
                    continue
                b = best(f, e, t, BE)
                a = {p: q[(f, p, e, t)] for p in INDIANA if (f, p, e, t) in q}
                if not b or not a:
                    continue
                ra = a[min(a, key=lambda p: float(a[p]["multi_qubit_gates"]))]
                o.append(red(float(ra["single_qubit_gates"]), float(b[1]["single_qubit_gates"])))
                m.append(red(float(ra["multi_qubit_gates"]), float(b[1]["multi_qubit_gates"])))
            labels.append(f"{e:g}")
            one_v.append(100 * med(o))
            multi_v.append(100 * med(m))
    x = range(len(labels))
    ax.bar([i - 0.2 for i in x], one_v, width=0.4, color="#4C72B0", label="1-qubit terms")
    ax.bar([i + 0.2 for i in x], multi_v, width=0.4, color="#DD8452", label="multi-qubit terms")
    ax.axhline(0, color="#333", linewidth=0.8)
    for k in (3.5, 7.5):
        ax.axvline(k, color="#999", linewidth=0.5, linestyle=":")
    ax.set_xticks(list(x))
    ax.set_xticklabels(labels, fontsize=7.5)
    for k, s in enumerate(SIZES):
        ax.text(4 * k + 1.5, 108, SNAME[s], ha="center", va="bottom", fontsize=8.5)
    ax.set_title(f"t = {TPLAIN[t]}", fontsize=10, pad=18)
    ax.set_ylim(-105, 105)
    ax.set_xlabel("ε", fontsize=9)
    ax.grid(True, axis="y", linestyle=":", linewidth=0.4)
for k in (0, 2):
    axes[k].set_ylabel("Median reduction on the\nIndiana analog machine (%)", fontsize=9)
axes[0].legend(fontsize=8, frameon=False, loc="lower left")
fig.tight_layout()
fig.savefig(OUT / "fig_be_vs_analog.png", dpi=200, bbox_inches="tight")
fig.savefig(OUT / "fig_be_vs_analog.pdf", bbox_inches="tight")
plt.close(fig)

# ---------------------------------------------------------------- 5.0.2 compact: which BE method wins, and by how much
tex = [r"% 5.0.2 winning BE method per program (generated)", r"\begin{tabular}{ll" + "r" * 6 + "}", r"\toprule",
       r" & & \multicolumn{4}{c}{Cheapest BE method (programs, of 276)} & \multicolumn{2}{c}{Winner's gate saving} \\",
       r"\cmidrule(lr){3-6}\cmidrule(lr){7-8}",
       r"$t$ & $\epsilon$ & " + " & ".join(BE.values()) + r" & vs.\ 2nd best & vs.\ worst \\", r"\midrule"]
md += ["## 5.0.2 (compact) Which BE method wins, and by how much\n",
       "Saving = 1 - winner's gates / other method's gates, median over all 276 programs.\n",
       "| t | ε | " + " | ".join(BE.values()) + " | saving vs 2nd best | saving vs worst |", "|---" * 8 + "|"]
for t in TIMES:
    for e in EPS:
        c, s2, sw = Counter(), [], []
        for f in files:
            if not all((f, p, e, t) in q for p in BE):
                continue
            g = sorted((tot(q[(f, p, e, t)]), p) for p in BE)
            c[g[0][1]] += 1
            s2.append(1 - g[0][0] / g[1][0])
            sw.append(1 - g[0][0] / g[-1][0])
        if not c:
            continue
        tex.append(f"${TNAME[t]}$ & {e:g} & " + " & ".join(str(c[p]) for p in BE)
                   + f" & {pct(med(s2))} & {pct(med(sw))}" + r" \\")
        md.append(f"| {TPLAIN[t]} | {e:g} | " + " | ".join(str(c[p]) for p in BE)
                  + f" | {100 * med(s2):.0f}% | {100 * med(sw):.0f}% |")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_be_wins.tex").write_text("\n".join(tex), encoding="utf-8")
md.append("")

# 5.2 for the paper: winners per dataset (Taylor and walk never win) and each method's gates over the best
tex = [r"% 5.2 BE algorithms: winners per dataset, gates over the best (generated)",
       r"\begin{tabular}{ll|rrr|rrr|rrrr}", r"\toprule",
       r" & & \multicolumn{3}{c|}{QSVT is best} & \multicolumn{3}{c|}{QSP is best} & "
       r"\multicolumn{4}{c}{Gates / best BE (median)} \\",
       r"$t$ & $\epsilon$ & S & M & L & S & M & L & QSVT & QSP & Taylor & Walk \\", r"\midrule"]
for t in TIMES:
    for e in EPS:
        c, ratios = Counter(), defaultdict(list)
        for f in files:
            if not all((f, p, e, t) in q for p in BE):
                continue
            g = {p: tot(q[(f, p, e, t)]) for p in BE}
            b = min(g, key=g.get)
            c[(b, size(f))] += 1
            for p in BE:
                ratios[p].append(g[p] / g[b])
        if not ratios:
            continue
        tex.append(f"${TNAME[t]}$ & {e:g} & " + " & ".join(str(c[(8, s)]) for s in SIZES) + " & "
                   + " & ".join(str(c[(9, s)]) for s in SIZES) + " & "
                   + " & ".join(f"{med(ratios[p]):.1f}$\\times$" for p in BE) + r" \\")
    if t != TIMES[-1]:
        tex.append(r"\midrule")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_be_algorithms_compact.tex").write_text("\n".join(tex), encoding="utf-8")

# ---------------------------------------------------------------- PennyLane (4.3, 4.4)
pl = {}
for name in ("pennylane_lcu.csv", "pennylane_lcu_short.csv"):
    pl.update(load(name, key_path=False))
ang = []
for name in ("pennylane_angle_stats.csv", "pennylane_angle_stats_short.csv"):
    p = R / name
    if p.exists():
        ang += list(csv.DictReader(open(p, newline="")))

# 4.3: QBlue best BE vs PennyLane, figure-9 style, one row per time
for method, label, fname in (("pl_est_exact", "PennyLane estimator (degree meeting ε)", "fig_pl_gates_estimator.png"),
                             ("pl_circuit", "PennyLane circuit (decomposed)", "fig_pl_gates_circuit.png")):
    rows = []
    for t in TIMES:
        recs = []
        for f in files:
            for e in EPS:
                k = (f, method, e, t)
                b = best(f, e, t, BE)
                if k in pl and b:
                    ours, theirs = tot(b[1]), tot(pl[k])
                    if ours > 0 and theirs > 0:
                        recs.append(dict(file_name=f, size=size(f), error=e, ours=ours, theirs=theirs,
                                         saving=red(ours, theirs)))
        if recs:
            rows.append((f"t = {TPLAIN[t]}, ", label, pd.DataFrame(recs)))
    if rows:
        plot_overall(rows, OUT / fname, f"QBlue (best BE algorithm) vs {label}",
                     "Programs sorted by PennyLane's count within each set.")

md += ["## 4.3 QBlue best BE vs PennyLane\n",
       "Median gate reduction of QBlue (positive: QBlue fewer).\n",
       "| t | ε | vs estimator S | M | L | vs circuit S | M | L |", "|---|---|---|---|---|---|---|---|"]
for t in TIMES:
    for e in EPS:
        cells = []
        for method in ("pl_est_exact", "pl_circuit"):
            for s in SIZES:
                v = [red(tot(best(f, e, t, BE)[1]), tot(pl[(f, method, e, t)])) for f in files
                     if size(f) == s and (f, method, e, t) in pl and best(f, e, t, BE)]
                cells.append(pct(med(v)).replace("\\", "") + (f" ({len(v)})" if v else ""))
        if any(c != "--" for c in cells):
            md.append(f"| {TPLAIN[t]} | {e:g} | " + " | ".join(cells) + " |")
md.append("")

# 4.4: PennyLane reliability / correctness per t x eps x set
md += ["## 4.4 PennyLane correctness and reliability\n",
       "Angle solver = PennyLane's poly_to_angles on the polynomial its own estimator assumes. Error bound = "
       "PennyLane's solver on a correctly budgeted polynomial; meets = its circuit's error ≤ ε. "
       "QBlue meets ε in every case by construction (truncation tail + scaling ≤ budget; phases checked).\n",
       "| t | ε | set | n | crash: |P|>1 | crash: ValueError | too large | angles, error > ε | angles, error ≤ ε | "
       "error bound met | exceeded | worst error / ε |", "|---" * 12 + "|"]
tex = [r"% 4.4 PennyLane angle solver and error bound (generated)", r"\begin{tabular}{lll" + "r" * 8 + "}",
       r"\toprule", r" & & & & \multicolumn{4}{c}{Angle solver} & \multicolumn{3}{c}{Error bound} \\",
       r"\cmidrule(lr){5-8}\cmidrule(lr){9-11}",
       r"$t$ & $\epsilon$ & Set & $n$ & $|P|>1$ & Root split & Too large & $>\epsilon$ & Met & Exceeded & Worst \\",
       r"\midrule"]
for t in TIMES:
    for e in EPS:
        for s in SIZES:
            sub = [r for r in ang if round(float(r["time"]), 4) == t and float(r["error"]) == e and size(r["file_name"]) == s]
            if not sub:
                continue
            crash_a = sum(r["pl_status"] == "crash" and "AssertionError" in r["message"] for r in sub)
            crash_v = sum(r["pl_status"] == "crash" and "AssertionError" not in r["message"] for r in sub)
            big = sum(r["pl_status"] == "too_large" for r in sub)
            over = sum(r["pl_status"] == "ok" and float(r["pl_total_error"]) > e for r in sub)
            okk = sum(r["pl_status"] == "ok" and float(r["pl_total_error"]) <= e for r in sub)
            v = [float(r["valid_total_error"]) for r in sub if r["valid_status"] == "ok" and r["valid_total_error"]]
            met = sum(x <= e for x in v)
            worst = max(v) / e if v else None
            md.append(f"| {TPLAIN[t]} | {e:g} | {SNAME[s]} | {len(sub)} | {crash_a} | {crash_v} | {big} | {over} | {okk} | "
                      f"{met} | {len(v) - met} | {worst:.1f}× |" if worst else "")
            tex.append(f"${TNAME[t]}$ & {e:g} & {SNAME[s]} & {len(sub)} & {crash_a} & {crash_v} & {big} & {over} & "
                       f"{met} & {len(v) - met} & " + (f"{worst:.1f}$\\times$" if worst else "--") + r" \\")
tex += [r"\bottomrule", r"\end{tabular}"]
(OUT / "tab_pl_reliability.tex").write_text("\n".join(tex), encoding="utf-8")
md.append("")

# 4.2: compile time vs program size. QBlue's LCU timings from qblue_results.csv are
# uncached (every job built its own pieces); later runs reuse cached piece counts, so
# their times are not compile times.
qt = load("qblue_results.csv")
# only the first setting of that run (pi/4, 0.02) built every piece from scratch;
# the later settings reused cached piece counts, so their times are not compile times
pairs = [(0.7854, 0.02)]
if pairs:
    fig, axes = plt.subplots(1, len(pairs), figsize=(4.2 * len(pairs), 3.4), sharey=True, squeeze=False)
    for ax, (t, e) in zip(axes[0], pairs):
        for lab, pts, col, mk in (
                ("QBlue QSP", [(int(r["program_size"]), float(r["compilation_time"])) for k, r in qt.items()
                               if k[1] == 9 and k[2] == e and k[3] == t], "#6A3D9A", "o"),
                ("QBlue QSVT", [(int(r["program_size"]), float(r["compilation_time"])) for k, r in qt.items()
                                if k[1] == 8 and k[2] == e and k[3] == t], "#B39DDB", "s"),
                ("PennyLane (real circuit)", [(int(r["program_size"]), float(r["seconds"])) for k, r in pl.items()
                                       if k[1] == "pl_circuit" and k[2] == e and k[3] == t], "#C44E52", "^"),
):
            if pts:
                x, y = zip(*pts)
                ax.scatter(x, np.maximum(y, 1e-3), s=6, color=col, marker=mk, label=lab, alpha=0.8)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_title(f"Compile time, t = {TPLAIN[t]}, ε = {e:g} (both build the full circuit)", fontsize=9)
        ax.set_xlabel("Pauli terms", fontsize=8)
        ax.grid(True, linestyle=":", linewidth=0.4)
    axes[0, 0].set_ylabel("Wall time (s)", fontsize=9)
    axes[0, 0].legend(fontsize=7, frameon=False)
    fig.tight_layout()
    fig.savefig(OUT / "fig_compile_time_real.png", dpi=200, bbox_inches="tight")
    fig.savefig(OUT / "fig_compile_time_real.pdf", bbox_inches="tight")
    plt.close(fig)

(OUT / "summary.md").write_text("\n".join(md), encoding="utf-8")
print("wrote", OUT)
