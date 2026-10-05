# particleSystem

```sh
make                 # QBlue, both baselines, then plots; 8 workers per runner
make qblue
make phoenix
make openfermion
make thirdparty      # Phoenix and OpenFermion
make plot
make clean           # Remove generated CSVs, plots, OCaml build, Python caches
# Optional overrides: make WORKERS=4 PYTHON=/path/to/python
```

Baseline targets reuse `results/qblue_results.csv`, running QBlue first if it is
missing. `make all` always reruns all experiments before generating plots.
Individual job failures are recorded in the CSVs and do not stop the Make
pipeline; setup errors still stop it. Running either threaded runner directly
returns a nonzero exit status for failed jobs unless `--allow-job-errors` is set.
