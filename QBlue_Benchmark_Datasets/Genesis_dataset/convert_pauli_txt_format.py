#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from decimal import Decimal
from pathlib import Path


OLD_TERM_RE = re.compile(r"^([IXYZ]+)\s+\(([^)]+)\)\s*$")
NEW_TERM_RE = re.compile(r"^([+-])\s+([^\s*]+)\s+\*\s+([IXYZ]+)\s*$")


def format_no_exponent(value: float) -> str:
    s = format(Decimal(str(value)), "f")
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in {"-0", ""} else s


def convert_line(line: str) -> str | None:
    s = line.strip()
    if not s:
        return None

    # Drop descriptive headers from the old files.
    if "mapping of" in s and "Hamiltonian in" in s:
        return None

    # Already converted, but re-normalize coefficient formatting (e.g. remove exponent notation).
    m_new = NEW_TERM_RE.match(s)
    if m_new:
        sign, coeff_str, pauli = m_new.groups()
        magnitude = format_no_exponent(abs(float(coeff_str)))
        return f"{sign} {magnitude} * {pauli}"

    m = OLD_TERM_RE.match(s)
    if not m:
        raise ValueError(f"Unrecognized line format: {s!r}")

    pauli, coeff_str = m.groups()
    coeff = complex(coeff_str)
    if abs(coeff.imag) > 1e-12:
        raise ValueError(f"Coefficient is not real: {coeff!r}")

    coeff_real = coeff.real
    sign = "+" if coeff_real >= 0 else "-"
    magnitude = format_no_exponent(abs(coeff_real))
    return f"{sign} {magnitude} * {pauli}"


def convert_file(src_path: Path, dst_path: Path) -> None:
    out_lines = []
    for line in src_path.read_text().splitlines():
        converted = convert_line(line)
        if converted is not None:
            out_lines.append(converted)

    dst_path.parent.mkdir(parents=True, exist_ok=True)
    dst_path.write_text(("\n".join(out_lines) + "\n") if out_lines else "")


def iter_input_files(src_root: Path):
    for path in src_root.rglob("*.txt"):
        if path.is_file():
            yield path


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Convert old Hamiltonian txt files from 'PAULI (coeff)' format to "
            "'+/- coeff * PAULI' format."
        )
    )
    parser.add_argument("src_dir", help="Directory containing old-format txt files")
    parser.add_argument("dst_dir", help="Directory to write converted txt files")
    args = parser.parse_args()

    src_root = Path(args.src_dir).expanduser().resolve()
    dst_root = Path(args.dst_dir).expanduser().resolve()

    if not src_root.exists() or not src_root.is_dir():
        raise SystemExit(f"Source directory does not exist or is not a directory: {src_root}")

    converted_count = 0
    for src_path in iter_input_files(src_root):
        rel_path = src_path.relative_to(src_root)
        dst_path = dst_root / rel_path
        convert_file(src_path, dst_path)
        converted_count += 1

    print(f"Converted {converted_count} file(s) from {src_root} to {dst_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
