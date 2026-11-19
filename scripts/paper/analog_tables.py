"""Indiana analog machine vs IBM digital, for the analog comparison in the discussion.

For each program, t and error bound, picks the best Trotter-based schedule on the Indiana
analog machine (fewest multi-qubit pulses, paths 11/12/13/16) and the best BE-based circuit on
IBM (fewest gates, paths 8/9/30/31), the same picks as tab_be_vs_analog.tex. Writes to
results/paper/:
  tab_be_vs_analog_counts.tex  median 1-qubit and multi-qubit counts per set
  indiana_vs_be_counts.csv     the same medians, unrounded
  indiana_vs_be_data.csv       every program's counts on every analog and BE path
"""
import csv
import statistics as st
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
R = ROOT / "results"
OUT = R / "paper"
INDIANA = {11: "Trotter-1", 12: "Trotter-2", 13: "QDrift", 16: "MarQSim"}
BE = {8: "QSVT", 9: "QSP", 30: "Taylor", 31: "Quantum walk"}
TIMES = {0.1963: r"\pi/16", 0.7854: r"\pi/4", 3.1416: r"\pi", 12.5664: r"4\pi"}
EPS = [0.1, 0.02, 0.002, 0.0002]
SIZES = {"small": "Small", "middle": "Medium", "large": "Large"}


def load():
    q = {}
    for name in ("qblue_results.csv", "lcu_results.csv", "grid_extra.csv"):
        p = R / name
        if p.exists():
            for r in csv.DictReader(open(p, newline="")):
                if r.get("status", "ok") == "ok":
                    q[(r["file_name"], int(r["path_flag"]), float(r["error"]), round(float(r["time"]), 4))] = r
    return q


def fmt(x):
    for d, s in ((1e9, "G"), (1e6, "M"), (1e3, "K")):
        if x >= d:
            return f"{x / d:.1f}{s}"
    return f"{x:.0f}"


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    q = load()
    files = sorted({k[0] for k in q})
    g = lambda r, c: float(r[c])
    size = lambda f: next((s for s in SIZES if f"/{s}/" in f), None)

    # every program, every analog and BE path
    raw = []
    for f in files:
        if not size(f):
            continue
        for t, tn in TIMES.items():
            for e in EPS:
                for paths, machine in ((INDIANA, "Indiana analog"), (BE, "IBM digital (BE)")):
                    for p, name in paths.items():
                        r = q.get((f, p, e, t))
                        if r:
                            raw.append({"program": Path(f).name, "set": SIZES[size(f)], "t": tn.replace("\\", ""),
                                        "error": e, "machine": machine, "algorithm": name, "path": p,
                                        "qubits": r["compilation_terms"] if p in BE else r["nqubit"],
                                        "one_qubit": r["single_qubit_gates"], "multi_qubit": r["multi_qubit_gates"],
                                        "steps": r["trotter_step"]})
    if not raw:
        raise SystemExit("no analog or BE rows in results/; run `make qblue lcu grid` first")
    with open(OUT / "indiana_vs_be_data.csv", "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(raw[0]))
        w.writeheader()
        w.writerows(raw)

    # medians of the best pick on each side
    tex = [r"% median counts: best Trotter on Indiana analog vs best BE on IBM digital (generated)",
           r"\begin{tabular}{ll|rrr|rrr|rrr|rrr}", r"\toprule",
           r" & & \multicolumn{6}{c|}{1-qubit terms} & \multicolumn{6}{c}{Multi-qubit terms} \\",
           r" & & \multicolumn{3}{c|}{Analog} & \multicolumn{3}{c|}{Digital (BE)} & \multicolumn{3}{c|}{Analog}"
           r" & \multicolumn{3}{c}{Digital (BE)} \\",
           r"$t$ & $\epsilon$ & S & M & L & S & M & L & S & M & L & S & M & L \\", r"\midrule"]
    rows = []
    for t, tn in TIMES.items():
        for e in EPS:
            cells = {}
            for s in SIZES:
                a1, am, d1, dm = [], [], [], []
                for f in files:
                    if size(f) != s:
                        continue
                    b = [q[(f, p, e, t)] for p in BE if (f, p, e, t) in q]
                    a = [q[(f, p, e, t)] for p in INDIANA if (f, p, e, t) in q]
                    if not b or not a:
                        continue
                    rb = min(b, key=lambda r: g(r, "single_qubit_gates") + g(r, "multi_qubit_gates"))
                    ra = min(a, key=lambda r: g(r, "multi_qubit_gates"))
                    a1.append(g(ra, "single_qubit_gates"))
                    am.append(g(ra, "multi_qubit_gates"))
                    d1.append(g(rb, "single_qubit_gates"))
                    dm.append(g(rb, "multi_qubit_gates"))
                cells[s] = [st.median(v) if v else float("nan") for v in (a1, d1, am, dm)]
                rows.append({"t": tn.replace("\\", ""), "error": e, "set": SIZES[s], "programs": len(a1),
                             "analog_1q": cells[s][0], "digital_1q": cells[s][1],
                             "analog_multi": cells[s][2], "digital_2q": cells[s][3]})
            line = [f"${tn}$", f"{e:g}"]
            for k in range(4):
                line += [fmt(cells[s][k]) if cells[s][k] == cells[s][k] else "--" for s in SIZES]
            tex.append(" & ".join(line) + r" \\")
        if t != 12.5664:
            tex.append(r"\midrule")
    tex += [r"\bottomrule", r"\end{tabular}"]
    (OUT / "tab_be_vs_analog_counts.tex").write_text("\n".join(tex) + "\n", encoding="utf-8")
    with open(OUT / "indiana_vs_be_counts.csv", "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    print(f"{len(raw)} program rows, {len(rows)} median rows -> {OUT}")


if __name__ == "__main__":
    main()
