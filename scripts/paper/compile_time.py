"""Compile time at every t and error bound: QBlue QSP built from scratch (no piece cache,
results/ctime.csv from `make ctime`) vs PennyLane building and decomposing its real circuit
(pl_circuit rows, programs up to 250 terms). Writes results/paper/fig_compile_time_all.*
and compile_time_all.md."""
import csv
import statistics as st
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

R = Path(__file__).resolve().parents[2] / "results"
(R / "paper").mkdir(parents=True, exist_ok=True)
TIMES = [0.1963, 0.7854, 3.1416, 12.5664]
TNAME = {0.1963: "π/16", 0.7854: "π/4", 3.1416: "π", 12.5664: "4π"}
EPS = [0.1, 0.02, 0.002, 0.0002]


def load(names, keep, col):
    out = {}
    for name in names:
        p = R / name
        if not p.exists():
            continue
        for r in csv.DictReader(open(p, newline="", encoding="utf-8")):
            if r["status"] == "ok" and keep(r):
                out[(r["file_name"], round(float(r["time"]), 4), float(r["error"]))] = (int(r["program_size"]),
                                                                                       float(r[col]))
    return out


qb = load(["ctime_more.csv", "ctime_4pi.csv", "ctime.csv"], lambda r: r["path_flag"] == "9", "compilation_time")
pl = load(["pennylane_lcu_short.csv", "pennylane_lcu.csv"], lambda r: r["method"] == "pl_circuit", "seconds")

fig, axes = plt.subplots(4, 4, figsize=(15, 12), sharex=True, sharey=True)
lines = ["| t | ε | programs | QBlue faster | median speedup | QBlue median (s) | PennyLane median (s) |",
         "|---|---|---|---|---|---|---|"]
for i, t in enumerate(TIMES):
    for j, e in enumerate(EPS):
        ax = axes[i, j]
        common = [k for k in pl if k[1:] == (t, e) and k in qb]
        if common:
            ax.scatter([pl[k][0] for k in common], [pl[k][1] for k in common], s=7, marker="^", color="#C44E52",
                       label="PennyLane")
            ax.scatter([qb[k][0] for k in common], [qb[k][1] for k in common], s=7, color="#6A3D9A",
                       label="QBlue QSP")
            sp = [pl[k][1] / qb[k][1] for k in common]
            faster = sum(s > 1 for s in sp)
            ax.set_title(f"t = {TNAME[t]}, ε = {e:g}: QBlue faster {faster}/{len(common)}, "
                         f"median {st.median(sp):.1f}×", fontsize=8.5)
            lines.append(f"| {TNAME[t]} | {e:g} | {len(common)} | {faster} | {st.median(sp):.1f}× | "
                         f"{st.median(qb[k][1] for k in common):.1f} | {st.median(pl[k][1] for k in common):.1f} |")
        else:
            ax.set_title(f"t = {TNAME[t]}, ε = {e:g}: no data yet", fontsize=8.5)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.grid(True, linestyle=":", linewidth=0.4)
        if i == 3:
            ax.set_xlabel("Pauli terms", fontsize=9)
        if j == 0:
            ax.set_ylabel("Compile time (s)", fontsize=9)
axes[0, 0].legend(fontsize=8, frameon=False, loc="upper left")
fig.suptitle("Compile time, QBlue QSP vs PennyLane, both building the full circuit "
             "(QBlue includes VOQC; programs PennyLane compiled, up to 250 terms)", fontsize=11)
fig.tight_layout(rect=(0, 0, 1, 0.97))
for ext in ("png", "pdf"):
    fig.savefig(R / "paper" / f"fig_compile_time_all.{ext}", dpi=200, bbox_inches="tight")
(R / "paper" / "compile_time_all.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
print("\n".join(lines))
