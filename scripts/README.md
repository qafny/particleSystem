# Benchmark scripts

## Dataset formats: MarQSim vs Genesis

- `QBlue_Benchmark_Datasets/MarQSim_dataset/*.txt` uses lines like:
  - `+ 1.1721681794967684 * IIIIIIIIIIIZ`
- `QBlue_Benchmark_Datasets/Genesis_dataset/**/**/*.txt` uses lines like:
  - `IIIIIIIIIIII (-5.152415944121773+0j)`

These are not the same format. The QBlue OCaml parser natively consumes the MarQSim-style format.

## Convert Genesis → MarQSim

```bash
python3 scripts/genesis_to_marqsim.py QBlue_Benchmark_Datasets/Genesis_dataset/LiH/JW_LiH_sto3g_4_electrons_12_spin_orbitals_Hamiltonian_631_paulis.txt -o /tmp/lih.marqsim.txt
```

## Run benchmark sweeps to CSV

This runs `mlqblue/performance.exe` across many inputs and parameter settings and writes a single CSV.

```bash
cd mlqblue
opam exec -- dune build
cd ..

python3 scripts/qblue_bench.py --dataset marqsim --out results_marqsim.csv --limit 2
```

Common options:
- `--errs 1e-1 1e-3`
- `--ts 0.1 0.5 1.0`
- `--pipelines auto std std2 qdrift marqsim` (maps to `performance.exe -p 0..4`)
- `--grouping none|qwc|fc` (passed to `performance.exe -g`; some pipelines may ignore it)
- `--timeout-s 1800`
- `--perf-exe path/to/performance.exe` (if your build output path differs)

To include Genesis (converted on-the-fly):
```bash
python3 scripts/qblue_bench.py --dataset all --out results_all.csv
```

## Notes on CSV columns

- `stdout_tail` falls back to stderr output when stdout is empty (most `performance.exe` debug logs go to stderr).
- `gates_in_json` / `gates_opt_json` include the full gate-count dictionaries so new/unknown gate keys are not dropped.

## Benchmark Phoenix (3rd-party baseline)

Phoenix lives under `thirdparty/phoenix` and depends on Qiskit + SciPy. Once you
have an environment that can `import qiskit` and `import scipy`, you can run:

```bash
python3 scripts/phoenix_bench.py \
  --inputs QBlue_Benchmark_Datasets/MarQSim_dataset/_Pauli_string_Ar.txt \
  --out results/phoenix_ar.csv \
  --ts 0.1
```

To run over all MarQSim inputs:
```bash
python3 scripts/phoenix_bench.py --dataset marqsim --out results/phoenix_marqsim.csv --ts 0.1
```

Phoenix also emits QBlue-comparable IBM-basis counts by default:
- `gates_opt_total`, `gates_opt_U1`, `gates_opt_U2`, `gates_opt_U3`, `gates_opt_CX`
- disable with `--no-ibm-counts`

## Benchmark Paulihedral and Tetris (vendored in Phoenix)

Phoenix vendors/refactors Paulihedral and Tetris under `thirdparty/phoenix/`.
These scripts run those baselines directly against `QBlue_Benchmark_Datasets`.

Paulihedral:

```bash
python3 scripts/paulihedral_bench.py \
  --dataset all \
  --out results/paulihedral.csv \
  --ts 0.1
```

Tetris:

```bash
python3 scripts/tetris_bench.py \
  --dataset all \
  --out results/tetris.csv \
  --ts 0.1
```

Notes:
- Both default to `--max-terms 5000` to skip extremely large Genesis instances (set `--max-terms 0` to disable).
- Both emit IBM-basis `gates_opt_*` columns by default for QBlue-style comparisons.

## Compare QBlue vs a baseline

Join two CSVs into a single wide CSV keyed by `(dataset, format, input_name, t)`:

```bash
python3 scripts/compare_bench_csv.py \
  --qblue results/qblue.csv \
  --phoenix results/phoenix.csv \
  --out results/qblue_vs_phoenix.csv
```

Paulihedral:

```bash
python3 scripts/compare_bench_csv.py \
  --qblue results/qblue.csv \
  --baseline results/paulihedral.csv \
  --baseline-name paulihedral \
  --out results/qblue_vs_paulihedral.csv
```

Tetris:

```bash
python3 scripts/compare_bench_csv.py \
  --qblue results/qblue.csv \
  --baseline results/tetris.csv \
  --baseline-name tetris \
  --out results/qblue_vs_tetris.csv
```

## One-shot runner (QBlue → baselines → compare)

`scripts/run.sh` runs datasets through QBlue, Phoenix, Paulihedral, and Tetris, then generates the joined CSV(s).

```bash
scripts/run.sh
```

Defaults / overrides (environment variables):
- `DATASET=all` (`marqsim` | `genesis` | `all`)
- `TS="0.1"` (space-separated list; passed to all)
- `QBLUE_ERRS="1e-1"` (Phoenix has no error bound; default is 1 value for 1:1 joins)
- `QBLUE_PIPELINES="std"`
- `QBLUE_GROUPING=none`
- `QBLUE_TIMEOUT_S=1800`
- `QBLUE_LIMIT=0` / `PHOENIX_LIMIT=0`
- `PHOENIX_ORDER_METHOD=trivial`
- `PHOENIX_MAX_TERMS=5000` (skip very large Hamiltonians by setting this > 0; set 0 to disable)
- `PAULIHEDRAL_MAX_TERMS=5000` / `PAULIHEDRAL_LIMIT=0`
- `TETRIS_MAX_TERMS=5000` / `TETRIS_LIMIT=0` / `TETRIS_SWAP_COEFFICIENT=3` / `TETRIS_K=10`
- `QBLUE_OUT=...` / `PHOENIX_OUT=...` / `PAULIHEDRAL_OUT=...` / `TETRIS_OUT=...`
- `COMPARE_PHOENIX_OUT=...` / `COMPARE_PAULIHEDRAL_OUT=...` / `COMPARE_TETRIS_OUT=...`

On SLURM, outputs default to `results/*_${SLURM_JOB_ID}.csv`.
