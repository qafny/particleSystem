# Benchmark scripts

## Supported datasets

- `mlqblue/DataSet1/**/*.txt`
- `mlqblue/DataSet2/**/*.txt`

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
- `--errs 0.5 0.1`
- `--ts 0.7853981633974483 0.19634954084936207` (`pi/4`, `pi/16`)
- `--pipelines auto std std2 qdrift marqsim` (maps to `performance.exe -p 0..4`)
- `--grouping none|qwc|fc` (passed to `performance.exe -g`; some pipelines may ignore it)
- `--timeout-s 1800`
- `--perf-exe path/to/performance.exe` (if your build output path differs)

To run both `DataSet1` and `DataSet2`:
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

## One-shot runner (QBlue → baselines → compare)

`scripts/run.sh` runs datasets through QBlue, Phoenix, Paulihedral, Tetris, and OpenFermion, then generates the joined CSV(s).

```bash
scripts/run.sh
```

Defaults / overrides (environment variables):
- `DATASET=all` (`dataset1` | `dataset2` | `all`)
- `TS="0.7853981633974483 0.19634954084936207"` (`pi/4 pi/16`; space-separated list; passed to all)
- `QBLUE_ERRS="0.5 0.1"`
- `QBLUE_PIPELINES="std"`
- `QBLUE_GROUPING=none`
- `QBLUE_TIMEOUT_S=1800`
- `QBLUE_LIMIT=0` / `PHOENIX_LIMIT=0`
- `PHOENIX_ORDER_METHOD=trivial`
- `PHOENIX_MAX_TERMS=5000` (skip very large Hamiltonians by setting this > 0; set 0 to disable)
- `PAULIHEDRAL_MAX_TERMS=5000` / `PAULIHEDRAL_LIMIT=0`
- `TETRIS_MAX_TERMS=5000` / `TETRIS_LIMIT=0` / `TETRIS_SWAP_COEFFICIENT=3` / `TETRIS_K=10`
- `OPENFERMION_MAX_TERMS=5000` / `OPENFERMION_LIMIT=0` / `OPENFERMION_TROTTER_NUMBER=1` / `OPENFERMION_TROTTER_ORDER=1`
- `QBLUE_OUT=...` / `PHOENIX_OUT=...` / `PAULIHEDRAL_OUT=...` / `TETRIS_OUT=...` / `OPENFERMION_OUT=...`
- `COMPARE_PHOENIX_OUT=...` / `COMPARE_PAULIHEDRAL_OUT=...` / `COMPARE_TETRIS_OUT=...` / `COMPARE_OPENFERMION_OUT=...`

On SLURM, outputs default to `results/*_${SLURM_JOB_ID}.csv`.

## Rebuild after merging `master`

When a merge updates the Coq sources, the extracted OCaml snapshot under
`mlqblue/qbluelib` needs to be refreshed as well. This script automates the
full rebuild:

```bash
QBLUE_OPAM_SWITCH=qblue ./scripts/rebuild_after_merge.sh
```

It does four things:
- rebuilds `coq/`
- reruns `extract_coq/extract.sh`
- refreshes `mlqblue/qbluelib` from `extract_coq/ml`
- rebuilds `mlqblue` and checks for `performance.exe`

If your opam switch has a different name, set `QBLUE_OPAM_SWITCH` accordingly.
