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
- `--pipelines std qdrift` (note: `std` maps to `-p 0`, `qdrift` maps to `-p 1`; `auto` is accepted for backwards compat and maps to `qdrift`)
- `--pipelines ab1 ab2` (note: `ab1` maps to `-p 2` and uses `mlqblue/ablib` 1st-order trotter; `ab2` maps to `-p 3` and uses 2nd-order/Strang)
- `--grouping none|qwc|fc` (passed to `performance.exe -g`; currently used by `ab1/ab2`, ignored by `std/qdrift`)
- `--timeout-s 1800`
- `--perf-exe path/to/performance.exe` (if your build output path differs)

To include Genesis (converted on-the-fly):
```bash
python3 scripts/qblue_bench.py --dataset all --out results_all.csv
```

## Notes on CSV columns

- `stdout_tail` falls back to stderr output when stdout is empty (most `performance.exe` debug logs go to stderr).
- `gates_in_json` / `gates_opt_json` include the full gate-count dictionaries so new/unknown gate keys are not dropped.
