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
  --inputs mlqblue/DataSet1/dir_100/MarqSim_Ar.txt \
  --perf-exe _build/default/performance.exe \
  --no-build \
  --out "results/dataset1_ar_${JOB_ID}.csv" \
  --errs 0.5 0.1 \
  --ts 0.7853981633974483 0.19634954084936207 \
  --pipelines std \
  --grouping none \
  --timeout-s 600
