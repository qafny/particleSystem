#!/bin/bash
#SBATCH -J marqsim_ar_smoke
#SBATCH -p general
#SBATCH -o marqsim_ar_smoke_%j.txt
#SBATCH -e marqsim_ar_smoke_%j.err
#SBATCH --mail-type=FAIL
#SBATCH --mail-user=gravjabr@iu.edu
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --time=00:30:00
#SBATCH --mem=8G
#SBATCH -A r00998

set -euo pipefail

module load python/3.11.13

# Make sure opam is on PATH if you installed it in ~/.local/bin
export PATH="$HOME/.local/bin:$PATH"

# Activate the switch you built everything in (adjust name if different)
eval "$(opam env --switch=qblue-coq816)"

cd "$HOME/particleSystem"

# Build performance.exe only if missing.
# (This avoids triggering compilation on clusters where the Coq-extracted
# qbluelib sources aren't in sync yet, but a previously-built binary exists.)
if [[ ! -x mlqblue/_build/default/performance.exe ]]; then
  cd mlqblue
  opam exec -- dune build
  cd ..
fi

# Run one MarQSim instance and write a CSV (good for validating columns).
python3 scripts/qblue_bench.py \
  --inputs QBlue_Benchmark_Datasets/MarQSim_dataset/_Pauli_string_Ar.txt \
  --perf-exe _build/default/performance.exe \
  --no-build \
  --out "results/marqsim_ar_${SLURM_JOB_ID}.csv" \
  --errs 1e-1 \
  --ts 0.1 \
  --pipelines std \
  --grouping none \
  --timeout-s 600
