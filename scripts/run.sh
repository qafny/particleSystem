#!/bin/bash
#
# Run QBlue, Phoenix, and OpenFermion benchmarks across all bucket datasets,
# t values, pipelines, and error bounds needed for paper plots.
#
# Each run_buckets.sh invocation can fan QBlue out across multiple cores.
# Set RUN_PAIR_JOBS>1 to process multiple (dataset, t) pairs at once.
# Output files: results/qblue_<tag>.csv, results/phoenix_<tag>.csv,
# and results/openfermion_<tag>.csv

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

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

CPU_COUNT="$(detect_cpu_count)"
RUN_PAIR_JOBS="$(sanitize_positive_int "${RUN_PAIR_JOBS:-1}" 1)"
if [[ -n "${RUN_BUCKETS_JOBS:-}" ]]; then
  RUN_BUCKETS_JOBS="$(sanitize_positive_int "${RUN_BUCKETS_JOBS}" 1)"
else
  RUN_BUCKETS_JOBS=$(( CPU_COUNT / RUN_PAIR_JOBS ))
  if (( RUN_BUCKETS_JOBS < 1 )); then
    RUN_BUCKETS_JOBS=1
  fi
fi

PIDS=()
LABELS=()

cleanup() {
  local pid
  for pid in "${PIDS[@]:-}"; do
    kill "$pid" 2>/dev/null || true
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
  if (( ${#PIDS[@]} >= RUN_PAIR_JOBS )); then
    wait_for_jobs
  fi
}

start_job() {
  local label="$1"
  shift
  echo "=== ${label} ===" >&2
  "$@" &
  PIDS+=("$!")
  LABELS+=("${label}")
  maybe_wait_for_slot
}

trap cleanup EXIT INT TERM

run_bucket_pair() {
  local dataset="$1" tag="$2" pipelines="$3" timeout_s="$4" t="$5"
  DATASET="${dataset}" RESULT_TAG="${tag}" \
  BENCHMARKS='qblue phoenix openfermion' \
  QBLUE_PIPELINES="${pipelines}" \
  QBLUE_ERRS='0.02 0.1 0.5' \
  QBLUE_TIMEOUT_S="${timeout_s}" \
  TS="${t}" \
  RUN_BUCKETS_JOBS="${RUN_BUCKETS_JOBS}" \
    scripts/run_buckets.sh
}

# Small: auto pipeline is fine, short timeout
run_small() {
  local tag="$1" t="$2"
  start_job "${tag}" run_bucket_pair bucket_s "${tag}" "std qdrift auto" 120 "${t}"
}

# Medium: auto with a capped timeout so MarQSim can't stall the whole run
run_medium() {
  local tag="$1" t="$2"
  start_job "${tag}" run_bucket_pair bucket_m "${tag}" "std qdrift auto" 300 "${t}"
}

# Large: skip auto (MarQSim OOMs/timeouts on large Hamiltonians)
run_large() {
  local tag="$1" t="$2"
  start_job "${tag}" run_bucket_pair bucket_l "${tag}" "std qdrift" 300 "${t}"
}

run_small  bucket_s_t_pi4  0.7853981633974483
run_small  bucket_s_t_pi16 0.19634954084936207

run_medium bucket_m_t_pi4  0.7853981633974483
run_medium bucket_m_t_pi16 0.19634954084936207

run_large  bucket_l_t_pi4  0.7853981633974483
run_large  bucket_l_t_pi16 0.19634954084936207

wait_for_jobs

echo "All done." >&2
