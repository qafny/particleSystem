#!/bin/bash
#
# Run QBlue and Phoenix benchmarks across all bucket datasets, t values, pipelines,
# and error bounds needed for paper plots.
#
# Each (dataset, t) pair runs sequentially; QBlue and Phoenix run in parallel within each pair.
# Output files: results/qblue_<tag>.csv and results/phoenix_<tag>.csv

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -f .venv/bin/activate ]]; then
  # shellcheck disable=SC1091
  source .venv/bin/activate
fi

mkdir -p results

# Small: auto pipeline is fine, short timeout
run_small() {
  local tag="$1" t="$2"
  echo "=== ${tag} ===" >&2
  DATASET=bucket_s RESULT_TAG="$tag" \
  BENCHMARKS='qblue phoenix' \
  QBLUE_PIPELINES='std qdrift auto' \
  QBLUE_ERRS='0.02 0.1 0.5' \
  QBLUE_TIMEOUT_S=120 \
  TS="$t" \
    scripts/run_buckets.sh
}

# Medium: auto with a capped timeout so MarQSim can't stall the whole run
run_medium() {
  local tag="$1" t="$2"
  echo "=== ${tag} ===" >&2
  DATASET=bucket_m RESULT_TAG="$tag" \
  BENCHMARKS='qblue phoenix' \
  QBLUE_PIPELINES='std qdrift auto' \
  QBLUE_ERRS='0.02 0.1 0.5' \
  QBLUE_TIMEOUT_S=300 \
  TS="$t" \
    scripts/run_buckets.sh
}

# Large: skip auto (MarQSim OOMs/timeouts on large Hamiltonians)
run_large() {
  local tag="$1" t="$2"
  echo "=== ${tag} ===" >&2
  DATASET=bucket_l RESULT_TAG="$tag" \
  BENCHMARKS='qblue phoenix' \
  QBLUE_PIPELINES='std qdrift' \
  QBLUE_ERRS='0.02 0.1 0.5' \
  QBLUE_TIMEOUT_S=300 \
  TS="$t" \
    scripts/run_buckets.sh
}

run_small  bucket_s_t_pi4  0.7853981633974483
run_small  bucket_s_t_pi16 0.19634954084936207

run_medium bucket_m_t_pi4  0.7853981633974483
run_medium bucket_m_t_pi16 0.19634954084936207

run_large  bucket_l_t_pi4  0.7853981633974483
run_large  bucket_l_t_pi16 0.19634954084936207

echo "All done." >&2
