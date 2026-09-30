# OpenFermion benchmark

From the repository root:

```sh
source .venv/bin/activate
cd mlqblue
python3 ../scripts/openfermion_bench.py -i job.csv -o result_openfermion.csv
```

For OpenFermion's tighter (more expensive) error calculation, add `--tight`:

```sh
python3 ../scripts/openfermion_bench.py -i job.csv -o result_openfermion_tight.csv --tight
```

To run jobs concurrently (from `mlqblue`):

```sh
python3 ../scripts/bench_threaded.py -i job.csv -o result_openfermion_threaded.csv -w 4 --tight
```

The wrapper accepts all options below plus `-w` / `--workers` (default `1`).
It runs one independent process per job and saves completed CSV rows and metadata
in input order after each completion. Concurrent jobs share CPU and memory,
so their timings reflect that load. Its default output is `result_openfermion_threaded.csv`.

Input uses the same format as QBlue; file paths are relative to your working directory:

```csv
file_name,error,time,path_flag
DataSet1/small/MarqSim_Ar_60.txt,0.1,0.7854,2
```

Only `path_flag=2` (second-order digital Trotter) is supported. Other paths are
recorded as `unsupported`. Output has the same columns as `gen_result.py`, with
bound details in `<output>.metadata.jsonl`. Existing output files are overwritten.

## Options

| Option | Meaning / default |
|---|---|
| `-i`, `--input` | Required job CSV |
| `-o`, `--output` | Result CSV; default `result_openfermion.csv` |
| `-e`, `--error` | Default tolerance: `0.1` |
| `-t`, `--time` | Default evolution time: `0.7854` |
| `-p`, `--path-flag` | Default path: `2` |
| `--tight` | Use `error_bound(..., tight=True)`; default is loose |
| `--max-terms` | Maximum effective Hamiltonian terms: `5000`; `0` disables |
| `--max-exponentials` | Maximum expanded Pauli exponentials: `1000000`; `0` disables |
| `-h`, `--help` | Show help |

CSV values override the error/time/path defaults. Failed jobs are recorded as
`error`; remaining jobs continue, and the process exits nonzero.

Step selection uses OpenFermion's `error_bound` and
`trotter_steps_required_propagator`. This is a leading-order error estimate,
not a certified bound on higher-order terms.

For first-time setup, run from the repository root (skip creation if `.venv` already exists):

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install qiskit ./thirdparty/OpenFermion
```
