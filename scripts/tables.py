"""Summarize results/*.csv into results/tables.md, results/tables.tex and
results/savings.csv (one row per experiment, program, error bound and time).

E0  Best QBlue algorithm vs OpenFermion second-order Trotter at OpenFermion's own step count.
E0P Best QBlue algorithm vs PHOENIX first-order Trotter at QBlue's first-order step count.
E1  First-order Trotter at the same step count: QBlue vs OpenFermion vs PHOENIX.
E2  Second-order Trotter, each with its own step calculation: QBlue vs OpenFermion.
E3  Best QBlue algorithm vs QBlue first-order Trotter.
S6  Algorithms inside QBlue, and analog vs digital targets.

Gate counts are totals (single-qubit + CX) unless a title says CX. Savings are
1 - ours / theirs; positive means QBlue uses fewer gates.
"""

import argparse
import csv
import statistics
from collections import defaultdict
from pathlib import Path

from benchmark import ROOT

DIGITAL = {1: "Trotter-1", 2: "Trotter-2", 3: "QDrift", 6: "MarQSim (CNOT)", 7: "MarQSim (CNOT+1q)"}
SIZES = ("small", "middle", "large")
SIZE_LABELS = {"small": "Small", "middle": "Medium", "large": "Large"}


def load(path):
    rows = {}
    if path.exists():
        with path.open(newline="") as source:
            for r in csv.DictReader(source):
                if r["status"] == "ok":
                    key = (r["file_name"], int(r.get("path_flag") or 2), float(r["error"]), round(float(r["time"]), 4))
                    rows[key] = r
    return rows


def size_class(file_name):
    return next((s for s in SIZES if f"/{s}/" in f"/{file_name}"), "other")


def total(row, before=False):
    suffix = "_bfopt" if before else ""
    return float(row["single_qubit_gates" + suffix]) + float(row["multi_qubit_gates" + suffix])


def cx(row, before=False):
    return float(row["multi_qubit_gates" + ("_bfopt" if before else "")])


def pct(v):
    return f"{100 * v:.1f}%"


def savings(triples):
    """(file, ours, theirs) -> (file, 1 - ours / theirs)."""
    return [(f, 1 - o / t) for f, o, t in triples if t > 0]


def by_size(pairs):
    groups = defaultdict(list)
    for file_name, value in pairs:
        groups[size_class(file_name)].append(value)
    return groups


def table(title, note, settings, measure):
    """Markdown table; measure(eps, t) -> list of (file_name, ours, theirs)."""
    lines = [f"### {title}\n", note + "\n",
             "| ε | t | median | mean | max | min | n | small | medium | large |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for eps, t in settings:
        pairs = savings(measure(eps, t))
        v = [x for _, x in pairs]
        if not v:
            lines.append(f"| {eps:g} | {t:g} | – | – | – | – | 0 | – | – | – |")
            continue
        groups = by_size(pairs)
        size = " | ".join(f"{pct(statistics.median(groups[s]))} ({pct(statistics.mean(groups[s]))})"
                          if groups[s] else "–" for s in SIZES)
        lines.append(f"| {eps:g} | {t:g} | {pct(statistics.median(v))} | {pct(statistics.mean(v))} | "
                     f"{pct(max(v))} | {pct(min(v))} | {len(v)} | {size} |")
    return lines + ["", "Size columns: median (mean).", ""]


def latex(title, settings, measure):
    """booktabs table: mean and median saving per size class and overall."""
    t_label = {0.7854: r"$\pi/4$", 0.1963: r"$\pi/16$"}
    head = " & ".join(rf"\multicolumn{{2}}{{c}}{{{SIZE_LABELS.get(s, s)}}}" for s in (*SIZES, "All"))
    lines = [r"% " + title, r"\begin{tabular}{ll" + "rr" * 4 + "}", r"\toprule",
             rf"$\epsilon$ & $t$ & {head} \\",
             "".join(rf"\cmidrule(lr){{{3 + 2 * i}-{4 + 2 * i}}}" for i in range(4)),
             " & & " + " & ".join(["Mean & Median"] * 4) + r" \\", r"\midrule"]
    for eps, t in settings:
        pairs = savings(measure(eps, t))
        groups = by_size(pairs)
        groups["All"] = [v for _, v in pairs]
        cells = []
        for s in (*SIZES, "All"):
            g = groups[s]
            cells += [f"{100 * statistics.mean(g):.1f}\\%", f"{100 * statistics.median(g):.1f}\\%"] if g else ["--", "--"]
        lines.append(f"{eps:g} & {t_label.get(t, f'{t:g}')} & " + " & ".join(cells) + r" \\")
    return lines + [r"\bottomrule", r"\end{tabular}", ""]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    q = load(args.csv_dir / "qblue_results.csv")
    of = load(args.csv_dir / "openfermion_results.csv")
    phx = load(args.csv_dir / "phoenix_results.csv")
    bounds = load(args.csv_dir / "bounds_results.csv")  # keyed with path 2
    settings = sorted({(k[2], k[3]) for k in q}, key=lambda s: (-s[1], s[0]))
    files = sorted({k[0] for k in q})

    def per_step(rows, key, before=False, count=total):
        return count(rows[key], before) / float(rows[key]["trotter_step"])

    def of_r(key):
        b = bounds.get(key)
        return int(b["of_r2_tight"] or b["of_r2_loose"]) if b else None

    def best(f, eps, t, paths=DIGITAL, count=total):
        options = {p: count(q[(f, p, eps, t)]) for p in paths if (f, p, eps, t) in q}
        if not options:
            return None, None
        p = min(options, key=lambda p: total(q[(f, p, eps, t)]))
        return p, options[p]

    def e0(eps, t, optimized=False):
        out = []
        for f in files:
            k2 = (f, 2, eps, t)
            p, ours = best(f, eps, t)
            r = of_r(k2)
            if p is not None and k2 in of and r is not None:
                out.append((f, ours, per_step(of, k2, before=not optimized) * r))
        return out

    def e0_qblue_steps(eps, t):
        """OpenFermion second-order circuit repeated QBlue's second-order step count."""
        out = []
        for f in files:
            k2 = (f, 2, eps, t)
            p, ours = best(f, eps, t)
            if p is not None and k2 in of and k2 in q:
                out.append((f, ours, per_step(of, k2, before=True) * float(q[k2]["trotter_step"])))
        return out

    def e0_phoenix(eps, t, count=total):
        """PHOENIX has no step calculation, so its first-order circuit is
        repeated QBlue's first-order step count (already applied in its CSV)."""
        out = []
        for f in files:
            k1 = (f, 1, eps, t)
            p, ours = best(f, eps, t, count=count)
            if p is not None and k1 in phx:
                out.append((f, ours, count(phx[k1])))
        return out

    def e1(eps, t, rows, before, count=total):
        return [(f, per_step(q, k, count=count), per_step(rows, k, before, count))
                for f in files if (k := (f, 1, eps, t)) in q and k in rows]

    def voqc(eps, t):
        return [(f, total(q[k]), total(q[k], before=True)) for f in files if (k := (f, 1, eps, t)) in q]

    def e2(eps, t):
        return [(f, total(q[k]), per_step(of, k, before=True) * of_r(k))
                for f in files if (k := (f, 2, eps, t)) in q and k in of and of_r(k)]

    def e2_steps(eps, t):
        return [(f, float(q[k]["trotter_step"]), of_r(k)) for f in files if (k := (f, 2, eps, t)) in q and of_r(k)]

    def e3(eps, t):
        out = []
        for f in files:
            p, ours = best(f, eps, t)
            if p is not None and (f, 1, eps, t) in q:
                out.append((f, ours, total(q[(f, 1, eps, t)])))
        return out

    def pair(ours, base, offset=0, count=total):
        def measure(eps, t):
            return [(f, count(q[(f, ours + offset, eps, t)]), count(q[(f, base, eps, t)]))
                    for f in files if (f, ours + offset, eps, t) in q and (f, base, eps, t) in q]
        return measure

    experiments = [
        ("E0", "Best QBlue algorithm vs OpenFermion (second order, OpenFermion's step count)",
         "QBlue picks the cheapest of Trotter-1, Trotter-2, QDrift, MarQSim at its own error bounds. "
         "OpenFermion: second-order circuit as generated, step count from `error_bound` (tight; loose above 3000 terms) "
         "and `trotter_steps_required_propagator`.", e0),
        ("E0b", "Same, against OpenFermion's circuit after Qiskit O3", "", lambda e, t: e0(e, t, True)),
        ("E0Q", "Best QBlue algorithm vs OpenFermion (second order, QBlue's second-order step count)",
         "Both sides use QBlue's verified step calculation: OpenFermion's second-order circuit as generated, "
         "repeated QBlue's second-order step count.", e0_qblue_steps),
        ("E0P", "Best QBlue algorithm vs PHOENIX (first order, QBlue's first-order step count)",
         "PHOENIX has no step calculation, so its first-order circuit is repeated QBlue's first-order "
         "step count (the commutator bound). PHOENIX counts are after its own optimization and Qiskit O3.", e0_phoenix),
        ("E0P-CX", "Same, CX only", "", lambda e, t: e0_phoenix(e, t, cx)),
        ("E1a", "First-order Trotter, same step count: QBlue vs OpenFermion", "", lambda e, t: e1(e, t, of, True)),
        ("E1b", "First-order Trotter, same step count: QBlue vs OpenFermion (CX)", "",
         lambda e, t: e1(e, t, of, True, cx)),
        ("E1c", "First-order Trotter, same step count: QBlue vs PHOENIX", "", lambda e, t: e1(e, t, phx, False)),
        ("E1d", "First-order Trotter, same step count: QBlue vs PHOENIX (CX)", "",
         lambda e, t: e1(e, t, phx, False, cx)),
        ("E1e", "VOQC inside QBlue: first-order Trotter after vs before optimization", "", voqc),
        ("E2", "Second-order Trotter, each with its own step calculation: QBlue vs OpenFermion",
         "QBlue: verified commutator bound. OpenFermion: leading-order estimate (arXiv:1312.1695).", e2),
        ("E3", "Best QBlue algorithm vs QBlue first-order Trotter", "", e3),
        ("S6a", "QDrift vs Trotter-1", "", pair(3, 1)),
        ("S6b", "QDrift vs Trotter-2", "", pair(3, 2)),
        ("S6c", "Trotter-2 vs Trotter-1", "", pair(2, 1)),
        ("S6d", "MarQSim (CNOT) vs QDrift", "", pair(6, 3)),
        ("S6e", "Indiana analog vs IBM digital, Trotter-1 (multi-qubit terms)", "", pair(1, 1, 10, cx)),
        ("S6f", "Indiana analog vs IBM digital, QDrift (multi-qubit terms)", "", pair(3, 3, 10, cx)),
        ("S6g", "IBM analog vs IBM digital, Trotter-1 (multi-qubit terms; 2-local Hamiltonians)", "",
         pair(1, 1, 20, cx)),
    ]

    md = ["# Results\n",
          f"{len(files)} Hamiltonians; all-to-all connectivity; QBlue run with `-arch a2a -sort`.\n"]
    tex = ["% Generated by scripts/tables.py; needs \\usepackage{booktabs}.", ""]
    rows = []
    for name, title, note, measure in experiments:
        md += table(f"{name}. {title}", note, settings, measure)
        tex += latex(f"{name}. {title}", settings, measure)
        for eps, t in settings:
            for f, ours, theirs in measure(eps, t):
                rows.append({"experiment": name, "file_name": f, "size": size_class(f), "error": eps, "time": t,
                             "ours": ours, "theirs": theirs, "saving": 1 - ours / theirs if theirs else ""})
        if name == "E2":
            md += ["### E2 (steps). QBlue's second-order step count divided by OpenFermion's\n",
                   "| ε | t | median ratio | max | min | n |", "|---|---|---|---|---|---|"]
            for eps, t in settings:
                v = [o / th for _, o, th in e2_steps(eps, t)]
                md.append(f"| {eps:g} | {t:g} | {statistics.median(v):.2f} | {max(v):.2f} | {min(v):.2f} | {len(v)} |"
                          if v else f"| {eps:g} | {t:g} | – | – | – | 0 |")
            md.append("")
    md += ["### Which algorithm is cheapest\n", "| ε | t | " + " | ".join(DIGITAL.values()) + " |",
           "|---|---|" + "---|" * len(DIGITAL)]
    for eps, t in settings:
        counts = defaultdict(int)
        for f in files:
            p, _ = best(f, eps, t)
            if p is not None:
                counts[p] += 1
        md.append(f"| {eps:g} | {t:g} | " + " | ".join(str(counts[p]) for p in DIGITAL) + " |")
    md.append("")
    (args.csv_dir / "tables.md").write_text("\n".join(md), encoding="utf-8")
    (args.csv_dir / "tables.tex").write_text("\n".join(tex), encoding="utf-8")
    with (args.csv_dir / "savings.csv").open("w", newline="") as target:
        writer = csv.DictWriter(target, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"Wrote tables.md, tables.tex and savings.csv in {args.csv_dir}")


if __name__ == "__main__":
    main()
