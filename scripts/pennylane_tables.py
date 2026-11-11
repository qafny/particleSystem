"""QBlue LCU vs PennyLane: results/lcu_results.csv against results/pennylane_lcu.csv.

For each PennyLane count (pl_est, pl_est_qbpoly, pl_circuit) and each QBlue
side (QSP, the same algorithm; QSVT; the best of QBlue's four LCU methods), per
(error, time) and size class: programs compared, programs where QBlue uses
fewer gates, and the median gate reduction (positive: QBlue uses fewer, as a
fraction of PennyLane's count; negative: PennyLane uses fewer, as a fraction of
QBlue's). QBlue is counted after VOQC; "before" uses its counts before VOQC,
the fairer match for PennyLane's unoptimized output. Writes
results/pennylane_tables.md.
"""

import csv
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from tables import SIZES, LCU, size_class, total, reduction, pct  # noqa: E402

PL = {"pl_est": "PennyLane estimator (its own degree)",
      "pl_est_exact": "PennyLane estimator at the degree that really meets the error",
      "pl_est_qbpoly": "PennyLane estimator at QBlue's degree",
      "pl_circuit": "PennyLane circuit at QBlue's degree"}
SIDES = {"QSP": [9], "QSVT": [8], "best LCU": list(LCU)}


def load():
    q, p = {}, {}
    with open(ROOT / "results/lcu_results.csv") as f:
        for r in csv.DictReader(f):
            if r["status"] == "ok" and int(r["path_flag"]) in LCU:
                q[(r["file_name"], int(r["path_flag"]), float(r["error"]), float(r["time"]))] = r
    with open(ROOT / "results/pennylane_lcu.csv") as f:
        for r in csv.DictReader(f):
            if r["status"] == "ok":
                p[(r["file_name"], r["method"], float(r["error"]), float(r["time"]))] = r
    return q, p


def pl_total(r):
    return float(r["single_qubit_gates"]) + float(r["multi_qubit_gates"])


def main():
    q, p = load()
    settings = sorted({(k[2], k[3]) for k in p}, key=lambda s: (s[1], -s[0]))
    md = ["# QBlue LCU vs PennyLane\n",
          "Positive: QBlue uses fewer gates (reduction of PennyLane's count); negative: PennyLane uses fewer. "
          "Cells: median reduction (QBlue wins / programs). QBlue after VOQC, and before VOQC in brackets.\n"]
    for m, title in PL.items():
        for side, paths in SIDES.items():
            md += [f"\n## {title} vs QBlue {side}\n",
                   "| t | error | " + " | ".join(SIZES) + " | all |", "|---|---|" + "---|" * (len(SIZES) + 1)]
            for eps, t in settings:
                cells = []
                for sz in list(SIZES) + ["all"]:
                    red, red_b, wins = [], [], 0
                    for (f, mm, e, tt), pr in p.items():
                        if mm != m or (e, tt) != (eps, t) or (sz != "all" and size_class(f) != sz):
                            continue
                        ours = [q[(f, k, e, tt)] for k in paths if (f, k, e, tt) in q]
                        if not ours:
                            continue
                        best = min(ours, key=total)
                        theirs = pl_total(pr)
                        red.append(reduction(total(best), theirs))
                        red_b.append(reduction(min(total(r, before=True) for r in ours), theirs))
                        wins += total(best) < theirs
                    cells.append(f"{pct(statistics.median(red))} [{pct(statistics.median(red_b))}] ({wins}/{len(red)})"
                                 if red else "–")
                md.append(f"| {t:g} | {eps:g} | " + " | ".join(cells) + " |")
    out = ROOT / "results/pennylane_tables.md"
    out.write_text("\n".join(md) + "\n")
    print(out)


if __name__ == "__main__":
    main()
