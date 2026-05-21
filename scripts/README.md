# Benchmark scripts

## Supported datasets

- `mlqblue/DataSet1/**/*.txt`
- `mlqblue/DataSet2/**/*.txt`
- `mlqblue/Buckets/S/**/*.txt`
- `mlqblue/Buckets/M/**/*.txt`
- `mlqblue/Buckets/L/**/*.txt`

Both datasets are MarQSim-style Hamiltonian text. `DataSet2` uses compact signs such as `+1.0 * XIII`, and the scripts accept both spacing styles.

Legacy Genesis inputs can still be passed explicitly to `qblue_bench.py` via `--inputs`; they are converted on the fly before calling `performance.exe`.

## Convert Genesis → MarQSim (legacy utility)

```bash
python3 scripts/genesis_to_marqsim.py QBlue_Benchmark_Datasets/Genesis_dataset/LiH/JW_LiH_sto3g_4_electrons_12_spin_orbitals_Hamiltonian_631_paulis.txt -o /tmp/lih.marqsim.txt
```

## Run benchmark sweeps to CSV

This runs `mlqblue/performance.exe` across many inputs and parameter settings and writes a single CSV.

```bash
cd mlqblue
opam exec -- dune build
cd ..

python3 scripts/qblue_bench.py --dataset dataset1 --out results_dataset1.csv --limit 2
```

Common options:
- `--dataset dataset1|dataset2|bucket_s|bucket_m|bucket_l|all|buckets`
- `--errs 0.5 0.1`
- `--ts 0.7853981633974483 0.19634954084936207` (`pi/4`, `pi/16`)
- `--pipelines auto std std2 qdrift marqsim` (maps to `performance.exe -p 0..4`)
- `--grouping none|qwc|fc` (recorded in the CSV)
- `--pass-grouping` (also pass `--grouping` to `performance.exe -g`; leave unset for the Zenodo/current CLI)
- `--timeout-s 1800`
- `--perf-exe path/to/performance.exe` (if your build output path differs)

To run both `DataSet1` and `DataSet2`:
```bash
python3 scripts/qblue_bench.py --dataset all --out results_all.csv
```

## Notes on CSV columns

- `compile_s` is the core synthesis/compilation time for the row.
- `wall_s` remains the broader end-to-end timed span used by the script.
- Baseline scripts also expose `ibm_basis_s` for the extra Qiskit/IBM-basis transpile/count pass.
- `qblue_bench.py` also exposes `optimize_s`, parsed from internal `performance.exe` timing output.
- `qblue_count_scope` records whether the QBlue gate counts are already full-circuit counts. For current JSON output this is `full_circuit`, so `plot_results.py` does not multiply those counts by `splitting_r` again.
- `stdout_tail` falls back to stderr output when stdout is empty (most `performance.exe` debug logs go to stderr).
- `gates_in_json` / `gates_opt_json` include the full gate-count dictionaries so new/unknown gate keys are not dropped.

## Benchmark Phoenix (3rd-party baseline)

Phoenix lives under `thirdparty/phoenix` and depends on Qiskit + SciPy. Once you
have an environment that can `import qiskit` and `import scipy`, you can run:

```bash
python3 scripts/phoenix_bench.py \
  --inputs mlqblue/DataSet1/dir_100/MarqSim_Ar.txt \
  --out results/phoenix_dataset1_ar.csv \
  --ts 0.7853981633974483 0.19634954084936207
```

To run over all `DataSet1` inputs:
```bash
python3 scripts/phoenix_bench.py --dataset dataset1 --out results/phoenix_dataset1.csv --ts 0.7853981633974483 0.19634954084936207
```

Phoenix also emits QBlue-comparable IBM-basis counts by default:
- `gates_opt_total`, `gates_opt_U1`, `gates_opt_U2`, `gates_opt_U3`, `gates_opt_CX`
- disable with `--no-ibm-counts`

## Benchmark Paulihedral and Tetris (vendored in Phoenix)

Phoenix vendors/refactors Paulihedral and Tetris under `thirdparty/phoenix/`.
These scripts run those baselines directly against `mlqblue/DataSet1` and `mlqblue/DataSet2`.

Paulihedral:

```bash
python3 scripts/paulihedral_bench.py \
  --dataset all \
  --out results/paulihedral.csv \
  --ts 0.7853981633974483 0.19634954084936207
```

Tetris:

```bash
python3 scripts/tetris_bench.py \
  --dataset all \
  --out results/tetris.csv \
  --ts 0.7853981633974483 0.19634954084936207
```

Notes:
- Both default to `--max-terms 5000` to skip extremely large instances (set `--max-terms 0` to disable).
- Both emit IBM-basis `gates_opt_*` columns by default for QBlue-style comparisons.

## Benchmark OpenFermion (3rd-party baseline)

OpenFermion lives under `thirdparty/OpenFermion`. The benchmark script imports
it from `thirdparty/OpenFermion/src` and needs the runtime dependencies from
OpenFermion's `dev_tools/requirements/deps/runtime.txt` installed into the same
Python environment. In this repo's `.venv`, the working install command was:

```bash
python3 -m pip install cirq-core deprecation h5py networkx pubchempy qiskit requests sympy
```

Smoke test:

```bash
python3 scripts/openfermion_bench.py \
  --inputs mlqblue/DataSet1/dir_100/MarqSim_Ar.txt \
  --out results/openfermion_dataset1_ar.csv \
  --ts 0.7853981633974483 0.19634954084936207
```

To run over all `DataSet1` inputs:

```bash
python3 scripts/openfermion_bench.py --dataset dataset1 --out results/openfermion.csv --ts 0.7853981633974483 0.19634954084936207
```

Notes:
- The script uses OpenFermion's `trotterize_exp_qubop_to_qasm(...)` API and translates its gate stream into qiskit for counting/transpile.
- Use `--trotter-number` and `--trotter-order` to change the OpenFermion Trotterization settings.
- Like Paulihedral and Tetris, it defaults to `--max-terms 5000` to avoid pathological large instances.

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

OpenFermion:

```bash
python3 scripts/compare_bench_csv.py \
  --qblue results/qblue.csv \
  --baseline results/openfermion.csv \
  --baseline-name openfermion \
  --out results/qblue_vs_openfermion.csv
```

## One-shot bucket runner

`scripts/run.sh` runs the bucket datasets through QBlue, Phoenix, and
OpenFermion for the error bounds, times, and QBlue pipelines used by the paper
plots. It regenerates CSV data only; it does not regenerate plots.

```bash
scripts/run.sh
```

By default, `scripts/run.sh` uses all detected cores inside one bucket/time job
at a time. This is equivalent to:

```bash
RUN_PAIR_JOBS=1 scripts/run.sh
```

With `RUN_PAIR_JOBS=1`, `RUN_BUCKETS_JOBS` defaults to the machine's detected
CPU count. To cap parallelism manually, use:

```bash
RUN_PAIR_JOBS=1 RUN_BUCKETS_JOBS=12 scripts/run.sh
```

Set `RUN_PAIR_JOBS>1` only if you intentionally want multiple bucket/time jobs
running at once; avoid also setting `RUN_BUCKETS_JOBS` high unless you want to
oversubscribe the machine.

Default CSV outputs:
- `results/qblue_bucket_*_t_pi16.csv`
- `results/qblue_bucket_*_t_pi4.csv`
- `results/phoenix_bucket_*_t_pi16.csv`
- `results/phoenix_bucket_*_t_pi4.csv`
- `results/openfermion_bucket_*_t_pi16.csv`
- `results/openfermion_bucket_*_t_pi4.csv`

Useful overrides (environment variables):
- `RUN_PAIR_JOBS=1` (how many dataset/time bucket jobs to run at once)
- `RUN_BUCKETS_JOBS=<cpu-count>` (parallelism inside each bucket job)
- `QBLUE_GROUPING=none`
- `QBLUE_LIMIT=0` / `PHOENIX_LIMIT=0`
- `PHOENIX_ORDER_METHOD=trivial`
- `PHOENIX_MAX_TERMS=5000` (skip very large Hamiltonians by setting this > 0; set 0 to disable)
- `OPENFERMION_MAX_TERMS=5000` / `OPENFERMION_LIMIT=0` / `OPENFERMION_TROTTER_NUMBER=1` / `OPENFERMION_TROTTER_ORDER=1`

For custom datasets, error bounds, times, QBlue pipelines, or QBlue timeouts,
call `scripts/run_buckets.sh` directly, or call the individual benchmark
scripts.

On SLURM, outputs default to `results/*_${SLURM_JOB_ID}.csv`.

## Regenerate plots

After the CSVs exist in `results/`, regenerate all plots known to
`scripts/plot_results.py` with:

```bash
MPLCONFIGDIR=/tmp/qblue-mpl python3 scripts/plot_results.py --out-dir results/plots
```

This reads the existing QBlue, Phoenix, and OpenFermion bucket CSVs from
`results/`, plus `results/result_0317.csv` when present, and overwrites the
generated plots in `results/plots/`.

## Rebuild after merging `master`

When a merge updates the Coq sources, the extracted OCaml snapshot under
`mlqblue/qbluelib` needs to be refreshed as well. This script automates the
full rebuild:

```bash
./scripts/rebuild_after_merge.sh
```

It does four things:
- rebuilds `coq/`
- reruns `extract_coq/extract.sh`
- refreshes `mlqblue/qbluelib` from `extract_coq/ml`
- rebuilds `mlqblue` and checks for `performance.exe`

The script hardcodes:
- `QBLUE_OPAM_SWITCH=qblue-coq816`
- `QBLUE_PYTHON_MODULE=python/3.11.13`

```bash
./scripts/rebuild_after_merge.sh
```
