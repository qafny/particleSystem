#!/bin/bash
#SBATCH -J run_marqsim_bench
#SBATCH -p general
#SBATCH -o run_marqsim_bench_%j.txt
#SBATCH -e run_marqsim_bench_%j.err
#SBATCH --mail-type=ALL
#SBATCH --mail-user=gravjabr@iu.edu
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --time=08:00:00
#SBATCH --mem=16G
#SBATCH -A r00998

set -euo pipefail

# (Optional) Load a python module if your pipeline needs it elsewhere.
module load python/3.11.13

# If you used modules for build tools (gcc/cmake/etc), load them here too.
# module load gcc

# Make sure opam is on PATH if you installed it in ~/.local/bin
export PATH="$HOME/.local/bin:$PATH"

# Use your opam root if you customized it (adjust if needed)
# export OPAMROOT="$HOME/.opam"
# or if you used the BigRed200 path:
# export OPAMROOT="/N/u/gravjabr/BigRed200/.opam"

# Activate the switch you built everything in (adjust name if different)
eval "$(opam env --switch=qblue-coq816)"

cd "$HOME/particleSystem"

# Build performance.exe if needed
cd mlqblue
opam exec -- dune build
cd ..

# Run all MarQSim inputs and write a single CSV.
# This sweeps the (err, t) settings from TODO.md.
python3 scripts/qblue_bench.py \
  --dataset marqsim \
  --out "results/marqsim_${SLURM_JOB_ID}.csv" \
  --errs 1e-1 1e-3 \
  --ts 0.1 0.5 1.0 \
  --pipelines std qdrift \
  --grouping none \
  --timeout-s 1800
