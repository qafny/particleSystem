# particleSystem

## Benchmarking (QBlue vs baselines)

See `scripts/README.md` for details.

Quick run:

```bash
cd ~/Development/particleSystem
source .venv/bin/activate
scripts/run.sh
```

Outputs (default):
- `results/qblue*.csv`
- `results/phoenix*.csv`
- `results/paulihedral*.csv`
- `results/tetris*.csv`
- `results/openfermion*.csv`
- `results/qblue_vs_phoenix*.csv`
- `results/qblue_vs_paulihedral*.csv`
- `results/qblue_vs_tetris*.csv`
- `results/qblue_vs_openfermion*.csv`

Common overrides:
- `TS="0.1"` (space-separated list)
- `QBLUE_ERRS="1e-1"` / `QBLUE_PIPELINES="std"` / `QBLUE_TIMEOUT_S=1800` / `QBLUE_LIMIT=0`
- `PHOENIX_LIMIT=0` / `PHOENIX_MAX_TERMS=5000`
- `PAULIHEDRAL_LIMIT=0` / `PAULIHEDRAL_MAX_TERMS=5000`
- `TETRIS_LIMIT=0` / `TETRIS_MAX_TERMS=5000`
- `OPENFERMION_LIMIT=0` / `OPENFERMION_MAX_TERMS=5000` / `OPENFERMION_TROTTER_NUMBER=1` / `OPENFERMION_TROTTER_ORDER=1`
- `QBLUE_OUT=...` / `PHOENIX_OUT=...` / `PAULIHEDRAL_OUT=...` / `TETRIS_OUT=...` / `OPENFERMION_OUT=...`
- `COMPARE_PHOENIX_OUT=...` / `COMPARE_PAULIHEDRAL_OUT=...` / `COMPARE_TETRIS_OUT=...` / `COMPARE_OPENFERMION_OUT=...`
