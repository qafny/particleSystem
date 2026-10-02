#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="$ROOT/.venv/bin/python"
OUTPUT_DIR="$ROOT/results"
WORKERS="${WORKERS:-1}"

cd "$ROOT/mlqblue"
if [[ ! -x _build/default/performance.exe ]]; then
    echo "Build QBlue first: cd mlqblue && dune build performance.exe" >&2
    exit 1
fi
mkdir -p "$OUTPUT_DIR"
QBLUE_OUTPUT="$(mktemp "$OUTPUT_DIR/.qblue_results.XXXXXX")"
trap 'rm -f -- "$QBLUE_OUTPUT"' EXIT

status=0
echo "Running QBlue experiments"
if "$PYTHON" gen_result_threaded.py \
    --input job.csv \
    --output "$QBLUE_OUTPUT" \
    --workers "$WORKERS"; then
    :
else
    result=$?
    if [[ "$result" -ne 1 ]]; then
        exit "$result"
    fi
    status=1
fi
if [[ ! -s "$QBLUE_OUTPUT" ]]; then
    echo "QBlue did not produce results" >&2
    exit 1
fi
mv -- "$QBLUE_OUTPUT" "$OUTPUT_DIR/qblue_results.csv"

echo "Running OpenFermion and Phoenix experiments"
if "$PYTHON" "$ROOT/scripts/benchmark_threaded.py" \
    --input "$OUTPUT_DIR/qblue_results.csv" \
    --output-dir "$OUTPUT_DIR" \
    --workers "$WORKERS"; then
    :
else
    result=$?
    if [[ "$result" -ne 1 ]]; then
        exit "$result"
    fi
    status=1
fi

echo "Results saved in $OUTPUT_DIR"
exit "$status"
