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

Experiments use an error bound ε = 0.1 and evolution time t = π/4, with
all-to-all connectivity. Jobs, errors, and times are listed in
`mlqblue/job.csv`.

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
