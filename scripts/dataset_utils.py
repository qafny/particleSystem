from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MLQBLUE = ROOT / "mlqblue"

DATASET_DIRS = {
    "dataset1": MLQBLUE / "DataSet1",
    "dataset2": MLQBLUE / "DataSet2",
}
DATASET_CHOICES = tuple(DATASET_DIRS.keys()) + ("all",)

MARQSIM_TERM_RE = re.compile(
    r"^\s*([+-])\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)\s*\*\s*([IXYZ]+)\s*$"
)
GENESIS_TERM_RE = re.compile(r"^\s*([IXYZ]+)\s+\(([^)]+)\)\s*$")


def detect_format(path: Path) -> str:
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for _ in range(50):
            line = f.readline()
            if not line:
                break
            s = line.strip()
            if not s:
                continue
            if MARQSIM_TERM_RE.match(s):
                return "marqsim"
            if GENESIS_TERM_RE.match(s):
                return "genesis"
    return "unknown"


def _sorted_txt_files(base: Path) -> list[Path]:
    files = list(base.rglob("*.txt"))
    return sorted(files, key=lambda p: (p.stat().st_size, str(p)))


def iter_dataset_input_files(dataset: str) -> list[Path]:
    if dataset == "all":
        files: list[Path] = []
        for name in ("dataset1", "dataset2"):
            files.extend(_sorted_txt_files(DATASET_DIRS[name]))
        return files
    if dataset in DATASET_DIRS:
        return _sorted_txt_files(DATASET_DIRS[dataset])
    raise ValueError(f"unknown dataset: {dataset}")


def dataset_label_for_path(path: Path) -> str:
    resolved = path.resolve()
    for base in DATASET_DIRS.values():
        if resolved.is_relative_to(base.resolve()):
            return base.name
    return "custom"
