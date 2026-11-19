"""Figure for RQ3 (PennyLane correctness and reliability), from the 4.4 table in
results/paper/summary.md (written by paper_figs.py). Top: what PennyLane's angle solver does
on each setting. Bottom: share of programs where PennyLane's circuit meets the requested
error bound."""
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker

OUT = Path(__file__).resolve().parents[2] / "results" / "paper"
TIMES = ["π/16", "π/4", "π", "4π"]
EPS = ["0.1", "0.02", "0.002", "0.0002"]
SIZES = ["Small", "Medium", "Large"]
COLORS = {"Small": "#4C72B0", "Medium": "#DD8452", "Large": "#55A868"}

text = (OUT / "summary.md").read_text(encoding="utf-8").split("## 4.4")[1].split("\n## ")[0]
data = {}
for line in text.splitlines():
    c = [x.strip() for x in line.strip().strip("|").split("|")]
    if len(c) == 12 and c[0] in TIMES:
        data[(c[0], c[1], c[2])] = list(map(int, c[3:11]))

CATS = [("Rejected (|P| > 1)", 1, "#C44E52"), ("Crash in root splitting", 2, "#E8A33D"),
        ("Too large to solve", 3, "#8C8C8C"), ("Angles, error > ε", 4, "#8172B3"),
        ("Angles, error ≤ ε", 5, "#55A868")]

fig, axes = plt.subplots(2, 4, figsize=(14, 6.4), sharey="row")
for j, t in enumerate(TIMES):
    ax = axes[0, j]
    bottom = [0.0] * len(EPS)
    for name, k, color in CATS:
        vals = []
        for e in EPS:
            rows = [data[(t, e, s)] for s in SIZES if (t, e, s) in data]
            n = sum(r[0] for r in rows)
            vals.append(sum(r[k] for r in rows) / n if n else 0)
        ax.bar(EPS, vals, bottom=bottom, color=color, width=0.65, label=name if j == 0 else None)
        bottom = [b + v for b, v in zip(bottom, vals)]
    ax.set_title(f"t = {t}", fontsize=10)
    ax.yaxis.set_major_formatter(mticker.PercentFormatter(1.0))

    ax = axes[1, j]
    for s in SIZES:
        y = [data[(t, e, s)][6] / data[(t, e, s)][0] for e in EPS]
        ax.plot(EPS, y, marker="o", markersize=4, linewidth=1.6, color=COLORS[s], label=f"PennyLane, {s}")
    ax.plot(EPS, [1] * len(EPS), color="#333", linestyle="--", linewidth=1.2, label="QBlue (all sizes)")
    ax.set_ylim(-0.04, 1.08)
    ax.yaxis.set_major_formatter(mticker.PercentFormatter(1.0))
    ax.set_xlabel("ε", fontsize=9)
    ax.grid(True, linestyle=":", linewidth=0.4)
axes[0, 0].set_ylabel("PennyLane angle solver\noutcome (share of programs)", fontsize=9)
axes[1, 0].set_ylabel("Programs whose circuit\nmeets ε", fontsize=9)
fig.legend(*axes[0, 0].get_legend_handles_labels(), fontsize=8, frameon=False, ncol=5,
           loc="upper center", bbox_to_anchor=(0.5, 1.04))
axes[1, 0].legend(fontsize=7.5, frameon=False, loc="lower left")
fig.tight_layout()
for ext in ("png", "pdf"):
    fig.savefig(OUT / f"fig_pl_reliability.{ext}", dpi=200, bbox_inches="tight")

tot = defaultdict(int)
for v in data.values():
    for i, x in enumerate(v):
        tot[i] += x
print("cases", tot[0], "rejected", tot[1], "root-split", tot[2], "too large", tot[3], "err>eps", tot[4],
      "ok", tot[5], "| error bound met", tot[6], "exceeded", tot[7], "unfinished", tot[0] - tot[6] - tot[7])
