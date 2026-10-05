OpenFermion synthesizes one first-order Trotter step and Phoenix uses same-weight grouping, simplification, trivial ordering, and the original cancellation passes from `jbg/202603`; both read Hamiltonians in Python using the current signed `coefficient * Pauli` format and multiply native before-optimization and optimized IBM-basis (`u1/u2/u3/cx`) gate counts by QBlue’s `trotter_step`, write exactly the `qblue_result.csv` columns for `path_flag=1` rows, and record failures above 10000 non-identity terms, with `compilation_terms=program_size*trotter_step` denoting repeated input terms.
The plots preserve the original scatter, mirrored optimization, and flower aesthetics, matching full input paths, errors, times, and pipelines to compare baseline total gate costs and synthesis-plus-optimization times with QBlue’s already full-circuit gate counts and reported compilation times, alongside QBlue’s pre-optimization QDrift/Trotter and analog/digital comparisons; the shared repetition factor estimates gate cost without proving equal achieved error, and times are never multiplied.

```sh
scripts/run.sh
# Optional concurrency: WORKERS=4 scripts/run.sh
.venv/bin/python scripts/openfermion_bench.py
.venv/bin/python scripts/phoenix_bench.py
.venv/bin/python scripts/benchmark_threaded.py --workers 4
.venv/bin/python scripts/plot_results.py
```

| Script | Defaults | Options |
| --- | --- | --- |
| `run.sh` | `mlqblue/job.csv` → `results/{qblue,openfermion,phoenix}_results.csv`; QBlue first, then both baselines | `WORKERS` (default 1) |
| `openfermion_bench.py` | `results/qblue_results.csv` → `results/openfermion_results.csv` | `--input`, `--output` |
| `phoenix_bench.py` | `results/qblue_results.csv` → `results/phoenix_results.csv` | `--input`, `--output` |
| `benchmark_threaded.py` | Both baselines → `results/{openfermion,phoenix}_results.csv`; one independent Python process per compiler/input/time, input order preserved, atomic saves after each completed job; timings reflect concurrent load | `--input`, `--output-dir`, `--workers` (default 1), `--compiler` (`phoenix` or `openfermion`; default both) |
| `plot_results.py` | CSVs in `results/` → PNG in `results/plots/` | `--csv-dir`, `--out-dir` |
