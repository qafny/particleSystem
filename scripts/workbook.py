"""Build results/qblue_evaluation.xlsx: every Trotter-family and LCU run, one row per
(program, error bound, time) with each method's gate count, and summary tables
computed from those rows with Excel formulas (so they update if the data does).

Sheets:
  README      what is where, the methods, the settings and the definitions
  Summary     per setting: Trotter family vs LCU reductions, cheapest method counts,
              median gate counts (formulas over the Gates sheet)
  Gates       one row per program and setting: total gates per method, best of each
              family, cheapest method and reductions (formulas)
  Runs        one row per compiled circuit (long format, for plotting)
  tables.md   every table in results/tables.md as values (OpenFermion, PHOENIX,
              analog and the rest), for reference

Run scripts/tables.py first; this reads the same CSVs with the same loader.
"""

import argparse
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path

from openpyxl import Workbook
from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
from openpyxl.utils import get_column_letter

from benchmark import ROOT
from tables import DIGITAL, LCU, load, size_class

METHODS = {**DIGITAL, **LCU}
RUNS = {"qblue_results.csv": "1: t = π/16, π/4", "lcu_results.csv": "2: t = π, 4π"}
T_LABELS = {0.1963: "π/16", 0.7854: "π/4", 3.1416: "π", 12.5664: "4π"}
SIZE_NAMES = {"small": "Small", "middle": "Medium", "large": "Large"}
SIZE_ORDER = ["small", "middle", "large"]

FONT = "Arial"
HEAD_FILL = PatternFill("solid", fgColor="1F3864")
SUB_FILL = PatternFill("solid", fgColor="D9E1F2")
FORMULA_FILL = PatternFill("solid", fgColor="F2F2F2")
THIN = Border(bottom=Side(style="thin", color="BFBFBF"))


def head(cell, sub=False):
    cell.font = Font(name=FONT, bold=True, color="000000" if sub else "FFFFFF")
    cell.fill = SUB_FILL if sub else HEAD_FILL
    cell.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)


def style_sheet(ws, widths, header_row=1, freeze="A2"):
    for row in ws.iter_rows():
        for c in row:
            if c.font is None or c.font.name != FONT:
                c.font = Font(name=FONT, bold=c.font.bold if c.font else False, color=c.font.color if c.font else None)
    for i, w in enumerate(widths, 1):
        ws.column_dimensions[get_column_letter(i)].width = w
    if freeze:
        ws.freeze_panes = freeze


def program_name(file_name):
    return Path(file_name).stem


def collect():
    """{(file, eps, t): {path: row}} from both runs, keeping only the 9 compared methods."""
    data, origin = defaultdict(dict), {}
    for csv_name, run in RUNS.items():
        for (f, p, eps, t), r in load(ROOT / "results" / csv_name).items():
            if p in METHODS:
                data[(f, eps, t)][p] = r
                origin[(eps, t)] = run
    return data, origin


def build(out):
    data, origin = collect()
    settings = sorted({(eps, t) for _, eps, t in data}, key=lambda s: (s[1], -s[0]))
    files = sorted({f for f, _, _ in data}, key=lambda f: (SIZE_ORDER.index(size_class(f)), program_name(f)))
    assert len({program_name(f) for f in files}) == len(files), "program names are not unique"
    wb = Workbook()
    wb.remove(wb.active)
    readme = wb.create_sheet("README")
    summary = wb.create_sheet("Summary")
    gates = wb.create_sheet("Gates")
    runs = wb.create_sheet("Runs")

    # ---------------- Runs: one row per compiled circuit ----------------
    run_cols = ["Run", "Program", "Size", "System qubits", "Pauli terms", "ε", "t", "t (label)", "Method", "Path",
                "1q gates", "Multi-qubit gates", "Total gates", "1q gates before VOQC", "Multi-qubit before VOQC",
                "Trotter steps / LCU segments", "Total qubits (LCU, incl. ancillas)", "Compile time (s)"]
    runs.append(run_cols)
    for c in runs[1]:
        head(c)
    i = 2
    for eps, t in settings:
        for f in files:
            for p, r in sorted(data.get((f, eps, t), {}).items(), key=lambda kv: list(METHODS).index(kv[0])):
                runs.append([origin[(eps, t)], program_name(f), SIZE_NAMES[size_class(f)], int(r["nqubit"]),
                             int(r["program_size"]), eps, float(r["time"]), T_LABELS[t], METHODS[p], p,
                             int(float(r["single_qubit_gates"])), int(float(r["multi_qubit_gates"])),
                             f"=K{i}+L{i}", int(float(r["single_qubit_gates_bfopt"])),
                             int(float(r["multi_qubit_gates_bfopt"])), int(float(r["trotter_step"])),
                             int(float(r["compilation_terms"])) if p in LCU else None, float(r["compilation_time"])])
                i += 1
    n_runs = i - 2
    for row in runs.iter_rows(min_row=2):
        for c in row[10:16]:
            c.number_format = "#,##0"
        row[12].fill = FORMULA_FILL
        row[17].number_format = "0.00"
    runs.auto_filter.ref = f"A1:{get_column_letter(len(run_cols))}{n_runs + 1}"
    style_sheet(runs, [16, 44, 9, 9, 9, 8, 9, 8, 18, 6, 14, 14, 14, 14, 14, 12, 12, 10])

    # ---------------- Gates: one row per program and setting ----------------
    m_cols = list(METHODS)  # columns I..Q
    col = {p: get_column_letter(9 + k) for k, p in enumerate(m_cols)}
    tro = f"{col[1]}{{r}}:{col[7]}{{r}}"   # I..M Trotter family
    lcu = f"{col[8]}{{r}}:{col[31]}{{r}}"  # N..Q LCU
    names = ["Setting", "Program", "Size", "System qubits", "Pauli terms", "ε", "t", "t (label)"]
    names += [METHODS[p] for p in m_cols]
    names += ["Best Trotter family", "Best Trotter method", "Best LCU", "Best LCU method", "Cheapest method",
              "Best Trotter vs best LCU", "vs QSVT", "vs QSP", "vs Taylor series", "vs Quantum walk",
              "Best LCU vs Trotter-1"]
    gates.append([None] * 8 + ["Total gates after VOQC (single-qubit + multi-qubit); blank = did not compile"]
                 + [None] * 8 + ["Formulas"] + [None] * 4
                 + ["Gate reduction: positive = Trotter family uses fewer gates"] + [None] * 4
                 + ["positive = LCU fewer"])
    gates.merge_cells("I1:Q1")
    gates.merge_cells("R1:V1")
    gates.merge_cells("W1:AA1")
    gates.append(names)
    for c in gates[1]:
        head(c, sub=True)
    for c in gates[2]:
        head(c)

    def reduction(ours, theirs):
        return f'=IF(OR({ours}="",{theirs}="",{ours}=0,{theirs}=0),"",IF({ours}<={theirs},1-{ours}/{theirs},-(1-{theirs}/{ours})))'

    blocks = {}  # setting -> {size or None: (first row, last row)}
    r = 3
    for eps, t in settings:
        label = f"ε = {eps:g}, t = {T_LABELS[t]}"
        start = r
        by_size = {}
        for s in SIZE_ORDER:
            s_start = r
            for f in [f for f in files if size_class(f) == s]:
                row = data.get((f, eps, t), {})
                if not row:
                    continue
                any_row = next(iter(row.values()))
                values = [label, program_name(f), SIZE_NAMES[s], int(any_row["nqubit"]), int(any_row["program_size"]),
                          eps, float(any_row["time"]), T_LABELS[t]]
                values += [int(float(row[p]["single_qubit_gates"]) + float(row[p]["multi_qubit_gates"]))
                           if p in row else None for p in m_cols]
                T, L = tro.format(r=r), lcu.format(r=r)
                values += [f"=MIN({T})", f"=INDEX($I$2:$M$2,MATCH(R{r},{T},0))",
                           f"=MIN({L})", f"=INDEX($N$2:$Q$2,MATCH(T{r},{L},0))",
                           f'=IF(R{r}<=T{r},S{r},U{r})',
                           reduction(f"R{r}", f"T{r}")]
                values += [reduction(f"R{r}", f"{col[p]}{r}") for p in LCU]
                values += [reduction(f"T{r}", f"I{r}")]
                gates.append(values)
                r += 1
            if r > s_start:
                by_size[s] = (s_start, r - 1)
        by_size[None] = (start, r - 1)
        blocks[(eps, t)] = (label, by_size)
    last = r - 1
    for row in gates.iter_rows(min_row=3, max_row=last):
        for c in row[8:17]:
            c.number_format = "#,##0"
        for c in row[17:22]:
            c.fill = FORMULA_FILL
        row[17].number_format = row[19].number_format = "#,##0"
        for c in row[22:28]:
            c.number_format = "0.0%"
            c.fill = FORMULA_FILL
    gates.auto_filter.ref = f"A2:AB{last}"
    style_sheet(gates, [22, 44, 9, 8, 8, 8, 9, 7] + [13] * 9 + [13, 16, 13, 13, 16] + [11] * 6, freeze="C3")

    # ---------------- Summary: formulas over Gates ----------------
    ws = summary
    ws["A1"] = "QBlue: Trotter-family vs LCU simulation, summary over 276 programs"
    ws["A1"].font = Font(name=FONT, bold=True, size=14)
    ws["A2"] = ("Every number below is a formula over the Gates sheet. Reduction: 1 − fewer/more, signed for the side "
                "that uses fewer gates (positive = Trotter family fewer, negative = LCU fewer), so values lie in (−100%, 100%).")
    ws["A2"].alignment = Alignment(wrap_text=True, vertical="top")
    ws.merge_cells("A2:N2")
    ws.row_dimensions[2].height = 30
    row = 4

    def section(title, note, cols):
        nonlocal row
        ws.cell(row, 1, title).font = Font(name=FONT, bold=True, size=12)
        if note:
            ws.cell(row + 1, 1, note).font = Font(name=FONT, italic=True, color="595959")
        row += 2
        for k, name in enumerate(["Run", "ε", "t"] + cols, 1):
            head(ws.cell(row, k, name))
        row += 1

    def rng(column, a, b):
        return f"Gates!{column}{a}:{column}{b}"

    # A. headline: best Trotter family vs best LCU
    section("A. Best Trotter-family method vs best LCU method (gate reduction)",
            "Positive: the Trotter family (Trotter-1/2, QDrift, MarQSim) uses fewer gates; negative: LCU does.",
            ["n", "Median", "Mean", "Max", "Min", "Median small", "Median medium", "Median large",
             "LCU cheapest (programs)", "Share LCU cheapest"])
    a_first = row
    for eps, t in settings:
        _, b = blocks[(eps, t)]
        a, z = b[None]
        R = rng("W", a, z)
        ws.append([origin[(eps, t)], eps, T_LABELS[t], f"=COUNT({R})", f"=MEDIAN({R})", f"=AVERAGE({R})",
                   f"=MAX({R})", f"=MIN({R})"]
                  + [f"=MEDIAN({rng('W', *b[s])})" if s in b else None for s in SIZE_ORDER]
                  + [f'=COUNTIF({R},"<0")', f"=L{row}/D{row}"])
        for k in range(5, 12):
            ws.cell(row, k).number_format = "0.0%"
        ws.cell(row, 13).number_format = "0.0%"
        row += 1
    a_last = row - 1
    row += 1

    # B. median reduction per comparison
    section("B. Median gate reduction, best Trotter-family method vs each LCU method",
            "Last column: best LCU method vs QBlue first-order Trotter (positive = LCU uses fewer).",
            ["vs best LCU", "vs QSVT", "vs QSP", "vs Taylor series", "vs Quantum walk", "Best LCU vs Trotter-1"])
    for eps, t in settings:
        a, z = blocks[(eps, t)][1][None]
        ws.append([origin[(eps, t)], eps, T_LABELS[t]]
                  + [f"=MEDIAN({rng(c, a, z)})" for c in ["W", "X", "Y", "Z", "AA", "AB"]])
        for k in range(4, 10):
            ws.cell(row, k).number_format = "0.0%"
        row += 1
    row += 1

    # C. which method is cheapest
    section("C. Which method is cheapest (number of programs)", "Ties go to the method listed first.",
            [METHODS[p] for p in m_cols] + ["n"])
    for eps, t in settings:
        label, b = blocks[(eps, t)]
        a, z = b[None]
        values = [origin[(eps, t)], eps, T_LABELS[t]]
        values += [f'=COUNTIF({rng("V", a, z)},"{METHODS[p]}")' for p in m_cols]
        values += [f"=SUM(D{row}:{get_column_letter(3 + len(m_cols))}{row})"]
        ws.append(values)
        row += 1
    row += 1

    # D. median gate counts
    section("D. Median total gates per method (after VOQC)", "Over the programs that compiled for that method.",
            [METHODS[p] for p in m_cols])
    for eps, t in settings:
        a, z = blocks[(eps, t)][1][None]
        ws.append([origin[(eps, t)], eps, T_LABELS[t]] + [f"=MEDIAN({rng(col[p], a, z)})" for p in m_cols])
        for k in range(4, 4 + len(m_cols)):
            ws.cell(row, k).number_format = "#,##0"
        row += 1
    style_sheet(ws, [17, 8, 7] + [13] * 10, freeze=None)

    # ---------------- tables.md as values ----------------
    md_path = ROOT / "results" / "tables.md"
    if md_path.exists():
        _tables_md(wb.create_sheet("tables.md"), md_path)

    # ---------------- README ----------------
    _readme(readme, settings, origin, len(files), n_runs, last - 2)
    wb.calculation.fullCalcOnLoad = True
    wb.save(out)
    print(f"Wrote {out}: {len(files)} programs, {len(settings)} settings, {n_runs} runs")


def _tables_md(ws, path):
    """Copy every markdown table; percentages become numbers, the rest stays text."""
    r, title, note = 1, None, None
    lines = path.read_text(encoding="utf-8").splitlines()
    ws.cell(r, 1, "All tables from results/tables.md (static values, generated by scripts/tables.py)").font = \
        Font(name=FONT, bold=True, size=14)
    r += 2
    k = 0
    while k < len(lines):
        line = lines[k]
        if line.startswith("#"):
            title = line.lstrip("#").strip()
            if line.startswith("## "):
                ws.cell(r, 1, title).font = Font(name=FONT, bold=True, size=13)
                r += 2
                title = None
        elif line.startswith("|"):
            if title:
                ws.cell(r, 1, title).font = Font(name=FONT, bold=True, size=11)
                r += 1
                if note:
                    ws.cell(r, 1, note).font = Font(name=FONT, italic=True, color="595959")
                    r += 1
            header = True
            while k < len(lines) and lines[k].startswith("|"):
                cells = [c.strip() for c in lines[k].strip().strip("|").split("|")]
                if not set("".join(cells)) <= set("-: "):
                    for j, v in enumerate(cells, 1):
                        c = ws.cell(r, j, _value(v))
                        if header:
                            head(c)
                        else:
                            c.font = Font(name=FONT)
                            if isinstance(c.value, float) and v.endswith("%"):
                                c.number_format = "0.0%"
                    header = False
                    r += 1
                k += 1
            r += 1
            title, note = None, None
            continue
        elif line.strip() and title:
            note = line.strip()
        k += 1
    for j in range(1, 14):
        ws.column_dimensions[get_column_letter(j)].width = 16 if j > 1 else 22


def _value(v):
    if re.fullmatch(r"-?\d+(\.\d+)?%", v):
        return float(v[:-1]) / 100
    if re.fullmatch(r"-?\d+(\.\d+)?(e-?\d+)?", v):
        return float(v) if "." in v or "e" in v else int(v)
    return v


def _readme(ws, settings, origin, n_programs, n_runs, n_rows):
    try:
        commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                                capture_output=True, text=True).stdout.strip() or os.environ.get("QBLUE_COMMIT", "unknown")
    except OSError:
        commit = "unknown"
    lines = [
        ("QBlue evaluation data: Trotter-family vs LCU Hamiltonian simulation", "title"),
        ("", None),
        ("Sheets", "h"),
        ("Summary: per setting, Trotter family vs LCU reductions, cheapest-method counts, median gate counts. All formulas over Gates.", None),
        (f"Gates: one row per program and setting ({n_rows} rows). Total gates per method, then formulas: best of each family, cheapest method, reductions.", None),
        (f"Runs: one row per compiled circuit ({n_runs} rows), long format for plotting: gates before and after VOQC, steps or segments, qubits, compile time.", None),
        ("tables.md: every table in results/tables.md as values, including the OpenFermion, PHOENIX and analog experiments.", None),
        ("", None),
        ("Methods (QBlue path number)", "h"),
        ("Trotter family: Trotter-1 (1), Trotter-2 (2), QDrift (3), MarQSim CNOT-weighted (6), MarQSim CNOT+1q-weighted (7).", None),
        ("LCU: QSVT (8), QSP / generalized QSP on the qubitization walk (9), Taylor series with OAA (30), quantum walk with Jacobi–Anger (31).", None),
        ("Compiled with QBlue (Coq, extracted to OCaml) and counted after VOQC, all-to-all connectivity.", None),
        ("", None),
        ("Settings", "h"),
        (f"{n_programs} programs from mlqblue/DataSet1 (small, medium, large).", None),
        ("Run 1 (results/qblue_results.csv): t ∈ {π/16, π/4}, ε ∈ {0.5, 0.1, 0.02}.", None),
        ("Run 2 (results/lcu_results.csv, make lcu): t ∈ {π, 4π}, ε ∈ {0.1, 0.02, 0.002, 0.0002}.", None),
        ("MarQSim did not compile the 19 programs with more than 2,000 Pauli terms (its size limit); those cells are blank. Every other method compiled every program.", None),
        ("", None),
        ("Definitions", "h"),
        ("Total gates = single-qubit + multi-qubit gates after VOQC.", None),
        ("Reduction = 1 − fewer/more, positive when the first side uses fewer gates and negative when the second does, so it stays in (−100%, 100%). Same as scripts/tables.py.", None),
        ("Best Trotter family = cheapest of methods 1, 2, 3, 6, 7 for that program and setting; best LCU = cheapest of 8, 9, 30, 31.", None),
        ("", None),
        ("Notes", "h"),
        ("Formulas recalculate when the file opens in Excel, Google Sheets or LibreOffice. Gray cells are formulas.", None),
        ("Summary medians use row ranges in Gates (rows are grouped by setting, then size), so re-sorting Gates breaks them; filter instead of sorting, or re-run scripts/workbook.py.", None),
        (f"Generated by scripts/workbook.py from the QBlue repository (commit {commit} plus uncommitted LCU changes on branch bhuwan/lcu-fix).", None),
    ]
    for k, (text, kind) in enumerate(lines, 1):
        c = ws.cell(k, 1, text)
        c.font = Font(name=FONT, bold=kind in ("title", "h"), size=14 if kind == "title" else 11)
        c.alignment = Alignment(wrap_text=True, vertical="top")
    ws.column_dimensions["A"].width = 130


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", type=Path, default=ROOT / "results/qblue_evaluation.xlsx")
    build(parser.parse_args().output)


if __name__ == "__main__":
    main()
