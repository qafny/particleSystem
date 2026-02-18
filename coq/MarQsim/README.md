# MarQSim Coq Translation

This directory contains a Coq translation of the Python modules under `src/`, plus a Coq model of the NetworkX subset used by MarQSim.

## File mapping

- `src/marqsim.py` -> `Marqsim.v`
- `src/overall.py` -> `Overall.v`
- `src/varying.py` -> `Varying.v`
- `src/spectra.py` -> `Spectra.v`
- `src/compile_time.py` -> `CompileTime.v`
- `src/exp.py` -> `Exp.v`
- `networkx` subset used by MarQSim -> `NetworkX.v`

## Notes on translation boundaries

- Deterministic structural logic is translated directly (Pauli datatypes, cost matrix construction, frequency counting, gate aggregation).
- NetworkX graph and min-cost-flow interfaces are translated into Coq datatypes/specification in `NetworkX.v`.
- Python-runtime-dependent parts are abstracted as `Parameter`s: file IO, plotting, subprocess execution, random sampling, NumPy linear algebra, Torch matrix exponentials.

## Build (if Coq is installed)

```bash
cd ocm/coq
coqc NetworkX.v
coqc Marqsim.v
coqc Overall.v
coqc Varying.v
coqc Spectra.v
coqc CompileTime.v
coqc Exp.v
```
