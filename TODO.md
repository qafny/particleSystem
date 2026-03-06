# TODO (benchmarks + paper)

This repo now has benchmarking harnesses under `scripts/`:
- QBlue sweep runner: `scripts/qblue_bench.py`
- Baselines (from `thirdparty/phoenix`): `scripts/phoenix_bench.py`, `scripts/paulihedral_bench.py`, `scripts/tetris_bench.py`
- CSV joiner: `scripts/compare_bench_csv.py`
- One-shot runner: `scripts/run.sh` (writes `results/*.csv`)

## Immediate (smoke + data collection)

- [x] Smoke test a single MarQSim instance (`scripts/marqsim.sh`)
- [x] Run QBlue over benchmark datasets to a CSV (`scripts/qblue_bench.py`)
- [x] Run baselines (Phoenix/Paulihedral/Tetris) over the same datasets to CSVs
- [x] Produce comparable “wide” CSVs: `results/qblue_vs_{phoenix,paulihedral,tetris}.csv`

## Evaluation (paper-facing)

- [ ] Add a table describing what each benchmark input represents (chemistry vs SYK, etc.)
- [ ] Report compilation time per benchmark; bucket into small/medium/large (by `n_terms`, `n_qubits`, or file size)
- [ ] Decide the sweep grid for QBlue:
  - error bounds (e.g. `1e-1`, `1e-3`; see `CHATS.txt` notes about too-small bounds)
  - times (e.g. `0.1`, `0.5`, `1.0`; and possibly `0.01` for std-pipeline stability)
  - pipelines (`std`, `std2`, `qdrift`, `marqsim`, `auto`)
  - grouping (`none`, `qwc`, `fc`) where applicable
- [ ] Compare QBlue vs prior work on the same Pauli-string Hamiltonians:
  - Phoenix (Paulihedral-derived)
  - Paulihedral
  - Tetris
  - 2QAN: deferred for now (expects circuit inputs; not directly comparable to Pauli-string Hamiltonian inputs)
- [ ] Decide how to handle very large Genesis instances (use `*_MAX_TERMS` filters or exclude from main plots)

## Optional / stretch

- [ ] Compare trotter-based pipelines vs LCU/Taylor-series pipeline (if still relevant + implemented)
- [ ] Compare compilation targets/backends (analog vs digital) if both are supported and meaningful
