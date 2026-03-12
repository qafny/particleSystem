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
OPENFERMION_OUT="${OPENFERMION_OUT:-results/openfermion${SUFFIX}.csv}"

COMPARE_PHOENIX_OUT="${COMPARE_PHOENIX_OUT:-results/qblue_vs_phoenix${SUFFIX}.csv}"
COMPARE_PAULIHEDRAL_OUT="${COMPARE_PAULIHEDRAL_OUT:-results/qblue_vs_paulihedral${SUFFIX}.csv}"
COMPARE_TETRIS_OUT="${COMPARE_TETRIS_OUT:-results/qblue_vs_tetris${SUFFIX}.csv}"
COMPARE_OPENFERMION_OUT="${COMPARE_OPENFERMION_OUT:-results/qblue_vs_openfermion${SUFFIX}.csv}"

# Default sweep: err in {0.5, 0.1}, t in {pi/4, pi/16}.
read -r -a QBLUE_ERRS_ARR <<< "${QBLUE_ERRS:-0.5 0.1}"
read -r -a TS_ARR <<< "${TS:-0.7853981633974483 0.19634954084936207}"
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

OPENFERMION_MAX_TERMS="${OPENFERMION_MAX_TERMS:-5000}"
OPENFERMION_LIMIT="${OPENFERMION_LIMIT:-0}"
OPENFERMION_TROTTER_NUMBER="${OPENFERMION_TROTTER_NUMBER:-1}"
OPENFERMION_TROTTER_ORDER="${OPENFERMION_TROTTER_ORDER:-1}"

# echo "[1/9] QBlue (${DATASET}) -> ${QBLUE_OUT}" >&2
# python3 scripts/qblue_bench.py \
#   --dataset "${DATASET}" \
#   --out "${QBLUE_OUT}" \
#   --errs "${QBLUE_ERRS_ARR[@]}" \
#   --ts "${TS_ARR[@]}" \
#   --pipelines "${QBLUE_PIPELINES_ARR[@]}" \
#   --grouping "${QBLUE_GROUPING}" \
#   --timeout-s "${QBLUE_TIMEOUT_S}" \
#   --limit "${QBLUE_LIMIT}"

echo "[2/9] Phoenix (${DATASET}) -> ${PHOENIX_OUT}" >&2
python3 scripts/phoenix_bench.py \
  --dataset "${DATASET}" \
  --out "${PHOENIX_OUT}" \
  --ts "${TS_ARR[@]}" \
  --order-method "${PHOENIX_ORDER_METHOD}" \
  --max-terms "${PHOENIX_MAX_TERMS}" \
  --limit "${PHOENIX_LIMIT}"

echo "[3/9] Paulihedral (${DATASET}) -> ${PAULIHEDRAL_OUT}" >&2
python3 scripts/paulihedral_bench.py \
  --dataset "${DATASET}" \
  --out "${PAULIHEDRAL_OUT}" \
  --ts "${TS_ARR[@]}" \
  --max-terms "${PAULIHEDRAL_MAX_TERMS}" \
  --limit "${PAULIHEDRAL_LIMIT}"

echo "[4/9] Tetris (${DATASET}) -> ${TETRIS_OUT}" >&2
python3 scripts/tetris_bench.py \
  --dataset "${DATASET}" \
  --out "${TETRIS_OUT}" \
  --ts "${TS_ARR[@]}" \
  --swap-coefficient "${TETRIS_SWAP_COEFFICIENT}" \
  --k "${TETRIS_K}" \
  --max-terms "${TETRIS_MAX_TERMS}" \
  --limit "${TETRIS_LIMIT}"

echo "[5/9] OpenFermion (${DATASET}) -> ${OPENFERMION_OUT}" >&2
python3 scripts/openfermion_bench.py \
  --dataset "${DATASET}" \
  --out "${OPENFERMION_OUT}" \
  --ts "${TS_ARR[@]}" \
  --trotter-number "${OPENFERMION_TROTTER_NUMBER}" \
  --trotter-order "${OPENFERMION_TROTTER_ORDER}" \
  --max-terms "${OPENFERMION_MAX_TERMS}" \
  --limit "${OPENFERMION_LIMIT}"

# echo "[6/9] Compare (Phoenix) -> ${COMPARE_PHOENIX_OUT}" >&2
# python3 scripts/compare_bench_csv.py \
#   --qblue "${QBLUE_OUT}" \
#   --baseline "${PHOENIX_OUT}" \
#   --baseline-name phoenix \
#   --out "${COMPARE_PHOENIX_OUT}"

# echo "[7/9] Compare (Paulihedral) -> ${COMPARE_PAULIHEDRAL_OUT}" >&2
# python3 scripts/compare_bench_csv.py \
#   --qblue "${QBLUE_OUT}" \
#   --baseline "${PAULIHEDRAL_OUT}" \
#   --baseline-name paulihedral \
#   --out "${COMPARE_PAULIHEDRAL_OUT}"

# echo "[8/9] Compare (Tetris) -> ${COMPARE_TETRIS_OUT}" >&2
# python3 scripts/compare_bench_csv.py \
#   --qblue "${QBLUE_OUT}" \
#   --baseline "${TETRIS_OUT}" \
#   --baseline-name tetris \
#   --out "${COMPARE_TETRIS_OUT}"

# echo "[9/9] Compare (OpenFermion) -> ${COMPARE_OPENFERMION_OUT}" >&2
# python3 scripts/compare_bench_csv.py \
#   --qblue "${QBLUE_OUT}" \
#   --baseline "${OPENFERMION_OUT}" \
#   --baseline-name openfermion \
#   --out "${COMPARE_OPENFERMION_OUT}"

echo "Done." >&2
