#!/bin/bash
#SBATCH -J run_all_bench
#SBATCH -p general
#SBATCH -o run_all_bench_%j.txt
#SBATCH -e run_all_bench_%j.err
#SBATCH --mail-type=END,FAIL
#SBATCH --mail-user=gravjabr@iu.edu
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --time=24:00:00
#SBATCH --mem=32G
#SBATCH -A r00998

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

module load python/3.11.13

export PATH="$HOME/.local/bin:$PATH"
eval "$(opam env --switch=qblue-coq816)"

# Default to the full benchmark sweep with no internal timeouts or term cutoffs.
export DATASET="${DATASET:-all}"
export QBLUE_TIMEOUT_S="${QBLUE_TIMEOUT_S:-0}"
export QBLUE_PARSE_TIMEOUT_S="${QBLUE_PARSE_TIMEOUT_S:-0}"
export QBLUE_TRANSLATION_TIMEOUT_S="${QBLUE_TRANSLATION_TIMEOUT_S:-0}"
export PHOENIX_MAX_TERMS="${PHOENIX_MAX_TERMS:-0}"
export PAULIHEDRAL_MAX_TERMS="${PAULIHEDRAL_MAX_TERMS:-0}"
export TETRIS_MAX_TERMS="${TETRIS_MAX_TERMS:-0}"
export OPENFERMION_MAX_TERMS="${OPENFERMION_MAX_TERMS:-0}"

echo "[run_all_bench] repo root: $ROOT" >&2
echo "[run_all_bench] dataset: $DATASET" >&2
echo "[run_all_bench] slurm job id: ${SLURM_JOB_ID:-none}" >&2

bash scripts/run.sh
