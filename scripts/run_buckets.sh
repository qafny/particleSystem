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

detect_cpu_count() {
  local n
  n="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
  if [[ ! "$n" =~ ^[0-9]+$ ]] || (( n < 1 )); then
    n=1
  fi
  printf '%s\n' "$n"
}

sanitize_positive_int() {
  local value="$1" fallback="$2"
  if [[ ! "$value" =~ ^[0-9]+$ ]] || (( value < 1 )); then
    value="$fallback"
  fi
  printf '%s\n' "$value"
}

if [[ -n "${SLURM_JOB_ID:-}" ]]; then
  SUFFIX="_${SLURM_JOB_ID}"
else
  SUFFIX=""
fi

DATASET="${DATASET:-buckets}"
RESULT_TAG="${RESULT_TAG:-$DATASET}"
RESULT_TAG="${RESULT_TAG//[^A-Za-z0-9_.-]/_}"

QBLUE_OUT="${QBLUE_OUT:-results/qblue_${RESULT_TAG}${SUFFIX}.csv}"
PHOENIX_OUT="${PHOENIX_OUT:-results/phoenix_${RESULT_TAG}${SUFFIX}.csv}"
PAULIHEDRAL_OUT="${PAULIHEDRAL_OUT:-results/paulihedral_${RESULT_TAG}${SUFFIX}.csv}"
TETRIS_OUT="${TETRIS_OUT:-results/tetris_${RESULT_TAG}${SUFFIX}.csv}"
OPENFERMION_OUT="${OPENFERMION_OUT:-results/openfermion_${RESULT_TAG}${SUFFIX}.csv}"

COMPARE_PHOENIX_OUT="${COMPARE_PHOENIX_OUT:-results/qblue_${RESULT_TAG}_vs_phoenix${SUFFIX}.csv}"
COMPARE_PAULIHEDRAL_OUT="${COMPARE_PAULIHEDRAL_OUT:-results/qblue_${RESULT_TAG}_vs_paulihedral${SUFFIX}.csv}"
COMPARE_TETRIS_OUT="${COMPARE_TETRIS_OUT:-results/qblue_${RESULT_TAG}_vs_tetris${SUFFIX}.csv}"
COMPARE_OPENFERMION_OUT="${COMPARE_OPENFERMION_OUT:-results/qblue_${RESULT_TAG}_vs_openfermion${SUFFIX}.csv}"

# Default sweep: err in {0.5, 0.1}, t in {pi/4, pi/16}.
read -r -a QBLUE_ERRS_ARR <<< "${QBLUE_ERRS:-0.5 0.1}"
read -r -a TS_ARR <<< "${TS:-0.7853981633974483 0.19634954084936207}"
read -r -a QBLUE_PIPELINES_ARR <<< "${QBLUE_PIPELINES:-std}"
read -r -a BENCHMARKS_ARR <<< "${BENCHMARKS:-qblue phoenix paulihedral tetris openfermion}"

_bench_enabled() { local b; for b in "${BENCHMARKS_ARR[@]}"; do [[ "$b" == "$1" ]] && return 0; done; return 1; }

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

CPU_COUNT="$(detect_cpu_count)"
RUN_BUCKETS_JOBS="$(sanitize_positive_int "${RUN_BUCKETS_JOBS:-$CPU_COUNT}" 1)"

PIDS=()
LABELS=()
TMP_PATHS=()

cleanup() {
  local pid path
  for pid in "${PIDS[@]:-}"; do
    kill "$pid" 2>/dev/null || true
  done
  for path in "${TMP_PATHS[@]:-}"; do
    [[ -n "$path" && -e "$path" ]] && rm -rf -- "$path"
  done
}

wait_for_jobs() {
  local failed=0
  local i
  for i in "${!PIDS[@]}"; do
    if ! wait "${PIDS[$i]}"; then
      echo "ERROR: ${LABELS[$i]} failed." >&2
      failed=1
    fi
  done
  PIDS=()
  LABELS=()
  return "$failed"
}

maybe_wait_for_slot() {
  if (( ${#PIDS[@]} >= RUN_BUCKETS_JOBS )); then
    wait_for_jobs
  fi
}

start_job() {
  local label="$1"
  shift
  echo "${label}" >&2
  "$@" &
  PIDS+=("$!")
  LABELS+=("${label}")
  maybe_wait_for_slot
}

merge_csv_shards() {
  local out="$1"
  shift
  local shard first=1
  for shard in "$@"; do
    [[ -f "$shard" ]] || continue
    if (( first )); then
      cat "$shard" > "$out"
      first=0
    else
      tail -n +2 "$shard" >> "$out"
    fi
  done
  if (( first )); then
    echo "ERROR: no QBlue shard outputs were produced for ${out}" >&2
    return 1
  fi
}

ensure_qblue_ready() {
  if [[ -x "$ROOT/mlqblue/_build/default/performance.exe" ]]; then
    return
  fi
  echo "[prep] Building QBlue performance.exe" >&2
  (
    cd "$ROOT/mlqblue"
    opam exec -- dune build
  )
}

run_qblue_combo() {
  local out="$1" err="$2" t="$3" pipeline="$4"
  python3 scripts/qblue_bench.py \
    --dataset "${DATASET}" \
    --out "${out}" \
    --errs "${err}" \
    --ts "${t}" \
    --pipelines "${pipeline}" \
    --grouping "${QBLUE_GROUPING}" \
    --timeout-s "${QBLUE_TIMEOUT_S}" \
    --limit "${QBLUE_LIMIT}" \
    --no-build
}

trap cleanup EXIT INT TERM

! _bench_enabled phoenix || start_job "[2/9] Phoenix (${DATASET}) -> ${PHOENIX_OUT}" \
  python3 scripts/phoenix_bench.py \
    --dataset "${DATASET}" \
    --out "${PHOENIX_OUT}" \
    --ts "${TS_ARR[@]}" \
    --order-method "${PHOENIX_ORDER_METHOD}" \
    --max-terms "${PHOENIX_MAX_TERMS}" \
    --limit "${PHOENIX_LIMIT}"

! _bench_enabled paulihedral || start_job "[3/9] Paulihedral (${DATASET}) -> ${PAULIHEDRAL_OUT}" \
  python3 scripts/paulihedral_bench.py \
    --dataset "${DATASET}" \
    --out "${PAULIHEDRAL_OUT}" \
    --ts "${TS_ARR[@]}" \
    --max-terms "${PAULIHEDRAL_MAX_TERMS}" \
    --limit "${PAULIHEDRAL_LIMIT}"

! _bench_enabled tetris || start_job "[4/9] Tetris (${DATASET}) -> ${TETRIS_OUT}" \
  python3 scripts/tetris_bench.py \
    --dataset "${DATASET}" \
    --out "${TETRIS_OUT}" \
    --ts "${TS_ARR[@]}" \
    --swap-coefficient "${TETRIS_SWAP_COEFFICIENT}" \
    --k "${TETRIS_K}" \
    --max-terms "${TETRIS_MAX_TERMS}" \
    --limit "${TETRIS_LIMIT}"

! _bench_enabled openfermion || start_job "[5/9] OpenFermion (${DATASET}) -> ${OPENFERMION_OUT}" \
  python3 scripts/openfermion_bench.py \
    --dataset "${DATASET}" \
    --out "${OPENFERMION_OUT}" \
    --ts "${TS_ARR[@]}" \
    --trotter-number "${OPENFERMION_TROTTER_NUMBER}" \
    --trotter-order "${OPENFERMION_TROTTER_ORDER}" \
    --max-terms "${OPENFERMION_MAX_TERMS}" \
    --limit "${OPENFERMION_LIMIT}"

QBLUE_SHARDS=()
if _bench_enabled qblue; then
  QBLUE_COMBO_COUNT=$(( ${#QBLUE_ERRS_ARR[@]} * ${#TS_ARR[@]} * ${#QBLUE_PIPELINES_ARR[@]} ))
  if (( RUN_BUCKETS_JOBS <= 1 || QBLUE_COMBO_COUNT <= 1 )); then
    start_job "[1/9] QBlue (${DATASET}) -> ${QBLUE_OUT}" \
      python3 scripts/qblue_bench.py \
        --dataset "${DATASET}" \
        --out "${QBLUE_OUT}" \
        --errs "${QBLUE_ERRS_ARR[@]}" \
        --ts "${TS_ARR[@]}" \
        --pipelines "${QBLUE_PIPELINES_ARR[@]}" \
        --grouping "${QBLUE_GROUPING}" \
        --timeout-s "${QBLUE_TIMEOUT_S}" \
        --limit "${QBLUE_LIMIT}"
  else
    ensure_qblue_ready
    QBLUE_TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/qblue_${RESULT_TAG}.XXXXXX")"
    TMP_PATHS+=("${QBLUE_TMP_DIR}")
    combo_idx=0
    for err in "${QBLUE_ERRS_ARR[@]}"; do
      for t in "${TS_ARR[@]}"; do
        for pipeline in "${QBLUE_PIPELINES_ARR[@]}"; do
          combo_idx=$((combo_idx + 1))
          shard_out="${QBLUE_TMP_DIR}/qblue_${combo_idx}.csv"
          QBLUE_SHARDS+=("${shard_out}")
          start_job "[QBlue ${combo_idx}/${QBLUE_COMBO_COUNT}] ${DATASET} err=${err} t=${t} pipeline=${pipeline}" \
            run_qblue_combo "${shard_out}" "${err}" "${t}" "${pipeline}"
        done
      done
    done
  fi
fi

wait_for_jobs

if (( ${#QBLUE_SHARDS[@]} > 0 )); then
  merge_csv_shards "${QBLUE_OUT}" "${QBLUE_SHARDS[@]}"
fi

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
