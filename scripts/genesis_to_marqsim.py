#!/usr/bin/env python3
"""
Convert a Genesis_dataset Hamiltonian file to the MarQSim_dataset text format.

Genesis format (example):
  Jordan-Wigner mapping of LiH Hamiltonian in sto3g basis.
  IIIIIIIIIIII (-5.152415944121773+0j)

MarQSim format (example):
  - 5.152415944121773 * IIIIIIIIIIII

Notes:
- We assume coefficients are real with an explicit "+0j" imaginary part.
- We skip non-data header lines that don't match the expected "(...+0j)" pattern.
"""

from __future__ import annotations

import argparse
import re
import sys
from decimal import Decimal, InvalidOperation, getcontext
from pathlib import Path


_LINE_RE = re.compile(
    r"^\s*([IXYZ]+)\s+\(\s*([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)\s*\+\s*0j\s*\)\s*$"
)

getcontext().prec = 80


def convert_text(genesis_text: str) -> str:
    out_lines: list[str] = []
    for raw_line in genesis_text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        m = _LINE_RE.match(line)
        if not m:
            continue
        paulis = m.group(1)
        coeff_s = m.group(2)
        try:
            coeff = Decimal(coeff_s)
        except InvalidOperation:
            continue

        sign = "+" if coeff >= 0 else "-"
        coeff_abs = -coeff if coeff < 0 else coeff

        # Avoid scientific notation: the OCaml lexer used by mlqblue rejects 'e'/'E'.
        coeff_out = format(coeff_abs, "f")
        if "." in coeff_out:
            coeff_out = coeff_out.rstrip("0").rstrip(".")
        if coeff_out == "":
            coeff_out = "0"

        out_lines.append(f"{sign} {coeff_out} * {paulis}")
    return "\n".join(out_lines) + ("\n" if out_lines else "")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path, help="Genesis_dataset *.txt file")
    ap.add_argument("-o", "--output", type=Path, default=None, help="Output file (default: stdout)")
    args = ap.parse_args()

    text = args.input.read_text(encoding="utf-8", errors="replace")
    converted = convert_text(text)
    if not converted.strip():
        print("ERROR: No Hamiltonian terms parsed. Is this a Genesis_dataset file?", file=sys.stderr)
        return 2

    if args.output is None:
        sys.stdout.write(converted)
    else:
        args.output.write_text(converted, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
