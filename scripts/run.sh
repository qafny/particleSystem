#!/bin/bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Prefer the repo-local venv if it exists (needed for phoenix_bench.py / qiskit).
if [[ -f .venv/bin/activate ]]; then
  # shellcheck disable=SC1091
  source .venv/bin/activate
fi

mkdir -p results

if [[ -n "${SLURM_JOB_ID:-}" ]]; then
  SUFFIX="_${SLURM_JOB_ID}"
else
  SUFFIX=""
fi

DATASET="${DATASET:-all}"

QBLUE_OUT="${QBLUE_OUT:-results/qblue${SUFFIX}.csv}"
PHOENIX_OUT="${PHOENIX_OUT:-results/phoenix${SUFFIX}.csv}"
PAULIHEDRAL_OUT="${PAULIHEDRAL_OUT:-results/paulihedral${SUFFIX}.csv}"
TETRIS_OUT="${TETRIS_OUT:-results/tetris${SUFFIX}.csv}"

COMPARE_PHOENIX_OUT="${COMPARE_PHOENIX_OUT:-results/qblue_vs_phoenix${SUFFIX}.csv}"
COMPARE_PAULIHEDRAL_OUT="${COMPARE_PAULIHEDRAL_OUT:-results/qblue_vs_paulihedral${SUFFIX}.csv}"
COMPARE_TETRIS_OUT="${COMPARE_TETRIS_OUT:-results/qblue_vs_tetris${SUFFIX}.csv}"

# Defaults chosen for easy 1:1 comparison with Phoenix (Phoenix has no "err").
read -r -a QBLUE_ERRS_ARR <<< "${QBLUE_ERRS:-1e-1}"
read -r -a TS_ARR <<< "${TS:-0.1}"
read -r -a QBLUE_PIPELINES_ARR <<< "${QBLUE_PIPELINES:-std}"

QBLUE_GROUPING="${QBLUE_GROUPING:-none}"
QBLUE_TIMEOUT_S="${QBLUE_TIMEOUT_S:-1800}"
QBLUE_LIMIT="${QBLUE_LIMIT:-0}"

PHOENIX_ORDER_METHOD="${PHOENIX_ORDER_METHOD:-trivial}"
PHOENIX_MAX_TERMS="${PHOENIX_MAX_TERMS:-5000}"
PHOENIX_LIMIT="${PHOENIX_LIMIT:-0}"

PAULIHEDRAL_MAX_TERMS="${PAULIHEDRAL_MAX_TERMS:-5000}"
PAULIHEDRAL_LIMIT="${PAULIHEDRAL_LIMIT:-0}"

TETRIS_MAX_TERMS="${TETRIS_MAX_TERMS:-5000}"
TETRIS_LIMIT="${TETRIS_LIMIT:-0}"
TETRIS_SWAP_COEFFICIENT="${TETRIS_SWAP_COEFFICIENT:-3}"
TETRIS_K="${TETRIS_K:-10}"

echo "[1/7] QBlue (${DATASET}) -> ${QBLUE_OUT}" >&2
python3 scripts/qblue_bench.py \
  --dataset "${DATASET}" \
  --out "${QBLUE_OUT}" \
  --errs "${QBLUE_ERRS_ARR[@]}" \
  --ts "${TS_ARR[@]}" \
  --pipelines "${QBLUE_PIPELINES_ARR[@]}" \
  --grouping "${QBLUE_GROUPING}" \
  --timeout-s "${QBLUE_TIMEOUT_S}" \
  --limit "${QBLUE_LIMIT}"

echo "[2/7] Phoenix (${DATASET}) -> ${PHOENIX_OUT}" >&2
python3 scripts/phoenix_bench.py \
  --dataset "${DATASET}" \
  --out "${PHOENIX_OUT}" \
  --ts "${TS_ARR[@]}" \
  --order-method "${PHOENIX_ORDER_METHOD}" \
  --max-terms "${PHOENIX_MAX_TERMS}" \
  --limit "${PHOENIX_LIMIT}"

echo "[3/7] Paulihedral (${DATASET}) -> ${PAULIHEDRAL_OUT}" >&2
python3 scripts/paulihedral_bench.py \
  --dataset "${DATASET}" \
  --out "${PAULIHEDRAL_OUT}" \
  --ts "${TS_ARR[@]}" \
  --max-terms "${PAULIHEDRAL_MAX_TERMS}" \
  --limit "${PAULIHEDRAL_LIMIT}"

echo "[4/7] Tetris (${DATASET}) -> ${TETRIS_OUT}" >&2
python3 scripts/tetris_bench.py \
  --dataset "${DATASET}" \
  --out "${TETRIS_OUT}" \
  --ts "${TS_ARR[@]}" \
  --swap-coefficient "${TETRIS_SWAP_COEFFICIENT}" \
  --k "${TETRIS_K}" \
  --max-terms "${TETRIS_MAX_TERMS}" \
  --limit "${TETRIS_LIMIT}"

echo "[5/7] Compare (Phoenix) -> ${COMPARE_PHOENIX_OUT}" >&2
python3 scripts/compare_bench_csv.py \
  --qblue "${QBLUE_OUT}" \
  --baseline "${PHOENIX_OUT}" \
  --baseline-name phoenix \
  --out "${COMPARE_PHOENIX_OUT}"

echo "[6/7] Compare (Paulihedral) -> ${COMPARE_PAULIHEDRAL_OUT}" >&2
python3 scripts/compare_bench_csv.py \
  --qblue "${QBLUE_OUT}" \
  --baseline "${PAULIHEDRAL_OUT}" \
  --baseline-name paulihedral \
  --out "${COMPARE_PAULIHEDRAL_OUT}"

echo "[7/7] Compare (Tetris) -> ${COMPARE_TETRIS_OUT}" >&2
python3 scripts/compare_bench_csv.py \
  --qblue "${QBLUE_OUT}" \
  --baseline "${TETRIS_OUT}" \
  --baseline-name tetris \
  --out "${COMPARE_TETRIS_OUT}"

echo "Done." >&2
