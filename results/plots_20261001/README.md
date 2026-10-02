# Experiment plots — 1 October 2026

Generated from `mlqblue/qblue_result.csv` and `mlqblue/result_openfermion.csv`.
No experiment metrics or source results were changed. All runs use ε=0.1 and t=0.7854.

## Coverage

- QBlue: 296 successful rows of 320; 24 errors (16 benzene parse timeouts and 8 MarQSim term-limit failures).
- OpenFermion: 35 successful path-2 rows; 4 term-limit errors; 1 missing path-2 row. Its other 280 rows are unsupported paths.
- Compiler comparisons: 35 matched inputs (3 Small, 21 Medium, 11 Large).
- Missing OpenFermion result: JW ethylene, 12 electrons / 20 spin orbitals, 2063 Pauli terms.
- OpenFermion term-limit failures: BK/JW benzene (368021 input terms) and BK/JW ethylene (8919 input terms).

## Initial observations

On all 35 matched inputs, QBlue reports more optimized total and multi-qubit gates.
The median per-input QBlue/OpenFermion total-gate ratio is 45,273× (range 694×–337,018×).
Reported step counts span 1,768–340,055 for QBlue versus 1–88 for OpenFermion.
These are comparisons of the reported circuits at equal requested tolerance;
the different error estimates do not establish equal achieved error.
Compilation timing uses only the existing compilation_time field; the runners' timing scopes differ.

## Figures

29 figures are supplied in both PNG and PDF, with matched input CSVs beside the comparisons.
The scaling plots include all successful inputs for each compiler; the parity and optimization
comparison plots use only matched inputs. Polar indices are mapped to filenames in adjacent CSVs.

- [t0.7854_path2/error0.1/compilation_time_vs_terms.png](t0.7854_path2/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path2/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path2/error0.1/gate_reduction.png](t0.7854_path2/error0.1/gate_reduction.png) · [PDF](t0.7854_path2/error0.1/gate_reduction.pdf)
- [t0.7854_path2/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path2/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path2/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path2/error0.1/scatter_qblue_vs_openfermion.png](t0.7854_path2/error0.1/scatter_qblue_vs_openfermion.png) · [PDF](t0.7854_path2/error0.1/scatter_qblue_vs_openfermion.pdf)
- [t0.7854_path2/error0.1/total_vs_terms.png](t0.7854_path2/error0.1/total_vs_terms.png) · [PDF](t0.7854_path2/error0.1/total_vs_terms.pdf)
- [qblue_t0.7854_error0.1/analog_vs_digital_multi_qubit_gates.png](qblue_t0.7854_error0.1/analog_vs_digital_multi_qubit_gates.png) · [PDF](qblue_t0.7854_error0.1/analog_vs_digital_multi_qubit_gates.pdf)
- [qblue_t0.7854_error0.1/analog_vs_digital_single_qubit_gates.png](qblue_t0.7854_error0.1/analog_vs_digital_single_qubit_gates.png) · [PDF](qblue_t0.7854_error0.1/analog_vs_digital_single_qubit_gates.pdf)
- [qblue_t0.7854_error0.1/qdrift_vs_trotter_polar.png](qblue_t0.7854_error0.1/qdrift_vs_trotter_polar.png) · [PDF](qblue_t0.7854_error0.1/qdrift_vs_trotter_polar.pdf)
- [t0.7854_path1/error0.1/compilation_time_vs_terms.png](t0.7854_path1/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path1/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path1/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path1/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path1/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path1/error0.1/total_vs_terms.png](t0.7854_path1/error0.1/total_vs_terms.png) · [PDF](t0.7854_path1/error0.1/total_vs_terms.pdf)
- [t0.7854_path11/error0.1/compilation_time_vs_terms.png](t0.7854_path11/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path11/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path11/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path11/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path11/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path11/error0.1/total_vs_terms.png](t0.7854_path11/error0.1/total_vs_terms.png) · [PDF](t0.7854_path11/error0.1/total_vs_terms.pdf)
- [t0.7854_path12/error0.1/compilation_time_vs_terms.png](t0.7854_path12/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path12/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path12/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path12/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path12/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path12/error0.1/total_vs_terms.png](t0.7854_path12/error0.1/total_vs_terms.png) · [PDF](t0.7854_path12/error0.1/total_vs_terms.pdf)
- [t0.7854_path13/error0.1/compilation_time_vs_terms.png](t0.7854_path13/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path13/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path13/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path13/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path13/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path13/error0.1/total_vs_terms.png](t0.7854_path13/error0.1/total_vs_terms.png) · [PDF](t0.7854_path13/error0.1/total_vs_terms.pdf)
- [t0.7854_path14/error0.1/compilation_time_vs_terms.png](t0.7854_path14/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path14/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path14/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path14/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path14/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path14/error0.1/total_vs_terms.png](t0.7854_path14/error0.1/total_vs_terms.png) · [PDF](t0.7854_path14/error0.1/total_vs_terms.pdf)
- [t0.7854_path3/error0.1/compilation_time_vs_terms.png](t0.7854_path3/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path3/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path3/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path3/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path3/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path3/error0.1/total_vs_terms.png](t0.7854_path3/error0.1/total_vs_terms.png) · [PDF](t0.7854_path3/error0.1/total_vs_terms.pdf)
- [t0.7854_path4/error0.1/compilation_time_vs_terms.png](t0.7854_path4/error0.1/compilation_time_vs_terms.png) · [PDF](t0.7854_path4/error0.1/compilation_time_vs_terms.pdf)
- [t0.7854_path4/error0.1/multi_qubit_gates_vs_terms.png](t0.7854_path4/error0.1/multi_qubit_gates_vs_terms.png) · [PDF](t0.7854_path4/error0.1/multi_qubit_gates_vs_terms.pdf)
- [t0.7854_path4/error0.1/total_vs_terms.png](t0.7854_path4/error0.1/total_vs_terms.png) · [PDF](t0.7854_path4/error0.1/total_vs_terms.pdf)
