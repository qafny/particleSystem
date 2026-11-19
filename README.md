# QBlue

QBlue is a verified compiler for Hamiltonian simulation. It takes a Hamiltonian
written as a sum of Pauli strings and compiles it into IBM digital circuits
(optimized with [VOQC](https://github.com/inQWIRE/SQIR)) or analog pulse
schedules. Supported algorithms include product formulas (first- and
second-order Trotterization, QDrift, MarQSim) and LCU-based methods (Taylor
series, qubitization, QSVT). The compiler and its correctness proofs are
written in Coq and extracted to OCaml.

This repository contains the Coq development, the OCaml compiler driver, and
the scripts that reproduce our benchmarks, including comparisons with
[OpenFermion](https://github.com/quantumlib/OpenFermion) and
[PHOENIX](https://github.com/iqubit-org/phoenix).

## Layout

| Path | Contents |
| --- | --- |
| `coq/` | Syntax and semantics, simulation algorithms, circuit synthesis, and proofs |
| `extract_coq/` | Extraction of the compiler from Coq to OCaml |
| `mlqblue/` | OCaml driver (`performance.exe`), Hamiltonian parser, and benchmark Hamiltonians (`DataSet1/`) |
| `scripts/` | Benchmark runners, OpenFermion and PHOENIX baselines, tables, plots, and circuit checks |

## Requirements

Linux, macOS, or WSL2 on Windows (native Windows is not supported), with:

- [opam](https://opam.ocaml.org/) and Coq 8.16.1, plus `coq-quantumlib`, `coq-sqir`, `coq-voqc`
- `dune`, `menhir`, `yojson`, `zarith`
- Python 3.10+

Install opam with your package manager (`sudo apt install opam libgmp-dev` on
Ubuntu, `brew install opam gmp` on macOS), then:

```sh
opam init
opam switch create qblue ocaml-base-compiler.4.12.0
eval $(opam env --switch=qblue)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.16.1 coq-quantumlib dune menhir yojson zarith
opam pin add coq-sqir https://github.com/inQWIRE/SQIR.git
opam pin add coq-voqc https://github.com/inQWIRE/SQIR.git

python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

## Build

```sh
make extract   # check the Coq proofs and extract the compiler into mlqblue/qbluelib
make build     # build mlqblue/_build/default/performance.exe
```

## Reproduce the benchmarks

```sh
make                # everything below, in order
make qblue          # QBlue on every job in mlqblue/job.csv
make openfermion    # OpenFermion Trotter circuits at the same step counts
make phoenix        # PHOENIX Trotter circuits at the same step counts
make bounds         # second-order step counts from QBlue's and OpenFermion's error bounds
make tables         # results/tables.md
make plot           # results/plots/
make clean
```

Options: `make WORKERS=4` sets the number of parallel jobs (default 8), and
`PYTHON=/path/to/python` overrides the interpreter. MarQSim builds a transition
graph over all Pauli strings and needs up to ~2 GB per job on the largest
Hamiltonians, so lower `WORKERS` on machines with less than 32 GB of memory.

Everything is written to `results/`:

| File | Contents |
| --- | --- |
| `qblue_results.csv` | Gate counts, step counts, and compile times for every QBlue job |
| `openfermion_results.csv`, `phoenix_results.csv` | Baseline gate counts for the same Hamiltonians and step counts |
| `bounds_results.csv` | Second-order step counts from QBlue's bound and OpenFermion's bound functions |
| `tables.md` | Summary tables used in the paper |
| `plots/` | Figures |

`mlqblue/job.csv` runs the Trotter-family and analog paths at t = π/16 and
π/4 with ε = 0.5, 0.1 and 0.02, all-to-all connectivity. The LCU runs below use
their own job file.

## LCU (block-encoding) methods

Besides the product formulas, QBlue compiles four block-encoding methods to
IBM digital circuits:

| `-p` | Method |
| --- | --- |
| 8 | QSVT (projector phases on the LCU block encoding) |
| 9 | QSP (generalized QSP on the qubitization walk) |
| 30 | Taylor series with LCU and one round of OAA |
| 31 | Quantum walk (powers of the walk combined by LCU, Jacobi-Anger) |

They're defined in `coq/QBlueTTS_v4.v`, `QBlueQuantumWalk.v`,
`QBlueQubitization.v` and `QBlueQSVT.v`. The QSVT phases are computed by
`qsvt_phases` in `QBlueQSVT.v`, and the QSP angles by layer stripping in
`extract_coq/src/networks/qsp_phases.py`. For these paths the CSV columns mean
slightly different things: `trotter_step` is the number of time segments and
`compilation_terms` is the total qubit count, ancillas included.

```sh
make lcu            # LCU and Trotter paths on mlqblue/job_lcu.csv -> results/lcu_results.csv
make check-lcu      # simulate small LCU circuits and compare with exp(-iHt)
make qsvt-phases    # check every QSVT phase sequence against its polynomial
```

`mlqblue/job_lcu.csv` covers t = π and 4π with ε = 0.1, 0.02, 0.002 and
0.0002, for paths 1, 2, 3, 6, 7, 8, 9, 30 and 31. Expect it to run for a
while, mostly because of the large Hamiltonians at 4π. `RESUME=1` picks up
where an interrupted run left off.

The paper uses the full grid of four times (π/16, π/4, π, 4π) and four error
bounds (0.1, 0.02, 0.002, 0.0002), for the Trotter, LCU and Indiana analog
paths. `job.csv` and `job_lcu.csv` only cover part of it, and `make grid` runs
the rest:

```sh
make grid           # mlqblue/job_grid.csv -> results/grid_extra.csv
```

That's every path at π/16 and π/4 with ε = 0.002 and 0.0002, QSVT again at
π/16 and π/4, and the analog paths (11, 12, 13, 16) at π and 4π. Rows in
`grid_extra.csv` take precedence over the other two files when the scripts
merge them.

The LCU circuits reuse a few big pieces (SELECT, the walk, the block encoding)
whose gate counts don't depend on ε or t, so the runner caches those counts in
`results/.lcu_cache`. This makes the gate counts much faster to get, but
it also means `compilation_time` in `lcu_results.csv` mostly measures cache
reads. For real compile times, `make ctime` runs QSP (path 9) with the cache
off, on the programs PennyLane can build at π/16, π/4 and π and on every
program at 4π (`mlqblue/job_ctime.csv`), and writes `results/ctime.csv`. To
time some other job file the same way:

```sh
cd mlqblue
QBLUE_LCU_CACHE= QBLUE_FLAGS="-arch a2a -sort" ../.venv/bin/python gen_result_threaded.py \
    --input job_lcu.csv --output ../results/lcu_ctime.csv --workers 8
```

MarQSim (paths 6, 7 and the analog 16) refuses Hamiltonians with more than
2000 terms, so those rows show up as errors for the largest programs. That's
expected.

### PennyLane baseline

We compare against PennyLane's GQSP time evolution, which is the same
algorithm as path 9. We keep PennyLane in its own environment, separate from
`.venv`:

```sh
python3 -m venv ~/pl-venv
~/pl-venv/bin/pip install pennylane==0.45.1 numpy scipy
```

```sh
make pennylane          # PennyLane on job_lcu.csv -> results/pennylane_lcu.csv
make pennylane-short    # same at π/16 and π/4 (job_pl_short.csv), angle solver included
make pennylane-angles   # PennyLane's angle solver on each setting's polynomial
make angle-bench        # PennyLane's solver vs ours as the degree grows
make pennylane-tables   # results/pennylane_tables.md
```

Use `PL_PYTHON=/path/to/python` if the environment lives somewhere else.
`pennylane_lcu.csv` has one row per program, setting and count. `pl_est` is
PennyLane's resource estimator at its own degree, `pl_est_exact` is the same
estimator at the degree that actually meets ε, `pl_est_qbpoly` is the estimator
at QBlue's degree, and `pl_circuit` is the real circuit, built and decomposed.
PennyLane can't build circuits for every program in reasonable time, so
`pl_circuit` stops at 250 Pauli terms (`--max-terms`).

The LCU part adds these files to `results/`:

| File | Contents |
| --- | --- |
| `lcu_results.csv` | Gate counts for the LCU and Trotter paths at t = π and 4π |
| `qsvt_phase_check.csv` | Phase error of every QSVT polynomial |
| `pennylane_lcu.csv` | PennyLane counts and compile times |
| `pennylane_angle_stats.csv` | Whether PennyLane's angle solver succeeds, and its error |
| `angle_solver_benchmark.jsonl` | Angle solver time and error against degree |
| `pennylane_tables.md` | QBlue vs PennyLane tables |
| `grid_extra.csv` | The rest of the 4 × 4 grid (`make grid`) |
| `ctime.csv` | QSP compile times with the cache off (`make ctime`) |
| `pennylane_lcu_short.csv`, `pennylane_angle_stats_short.csv` | PennyLane at π/16 and π/4 |

### Paper tables and figures

Once the runs are done, `make paper` builds the evaluation and discussion
tables and figures into `results/paper/`. It uses whatever results exist, so
you can rerun it after any single run finishes.

```sh
make qblue lcu grid ctime                 # QBlue, every path, time and error bound
make pennylane pennylane-short pennylane-angles
make paper
```

| File in `results/paper/` | What it shows |
| --- | --- |
| `fig_compile_time_all` | Compile time, QBlue vs PennyLane, every t and ε |
| `fig_pl_gates_circuit` | QBlue's best BE circuit vs PennyLane's decomposed circuit |
| `fig_pl_reliability` | PennyLane's angle solver outcomes, and how often its circuit meets ε |
| `fig_be_vs_trotter` | Best BE vs best Trotter: share of wins, gate ratio, qubit ratio |
| `tab_be_algorithms_compact.tex` | Which BE method wins per set, and each method's gates over the best |
| `fig_be_vs_analog`, `tab_be_vs_analog.tex` | Best Trotter on the Indiana analog machine vs best BE on IBM, median reduction |
| `tab_be_vs_analog_counts.tex`, `indiana_vs_be_*.csv` | The same comparison as raw counts |
| `summary.md` | All of the above as markdown tables |

The scripts live in `scripts/paper/` and need only the packages in
`requirements.txt`.

## Compiling a single Hamiltonian

```sh
cd mlqblue
./_build/default/performance.exe DataSet1/small/MarqSim_Ar_60.txt -e 0.1 -t 0.7854 -p 2 -arch a2a -sort
```

The output is a JSON record with gate counts before and after optimization and
the number of Trotter steps. See [`mlqblue/README.md`](mlqblue/README.md) for
all compilation paths (`-p`) and the datasets.

Hamiltonians are plain text, one signed term per line:

```
+0.403532174012516 * IIZIIIII
-0.027410744582439 * XYYIIIII
```

Character *i* of each Pauli string acts on qubit *i*.
