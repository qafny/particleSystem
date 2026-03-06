#!/bin/bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Prefer the repo-local venv if it exists.
if [[ -f .venv/bin/activate ]]; then
  # shellcheck disable=SC1091
  source .venv/bin/activate
fi

JOB_ID="${SLURM_JOB_ID:-local}"

python3 scripts/qblue_bench.py \
  --inputs QBlue_Benchmark_Datasets/MarQSim_dataset/_Pauli_string_Ar.txt \
  --perf-exe _build/default/performance.exe \
  --no-build \
  --out "results/marqsim_ar_${JOB_ID}.csv" \
  --errs 1e-1 \
  --ts 0.1 \
  --pipelines std \
  --grouping none \
  --timeout-s 600
