# Smallest shared input: compiler comparison

Input: `mlqblue/DataSet1/small/MarqSim_Ar_60.txt` (8 qubits, 60 distinct nonidentity terms).
Requested tolerance 0.1; evolution time 0.7854; path 2 (second-order Trotter).
The input SHA-256 matches the saved OpenFermion metadata. Maximum absolute
coefficient is 1.5034077382892697; sum of absolute coefficients is 14.603032979218646.

## Reproduced result counts

| Quantity | QBlue | OpenFermion |
|---|---:|---:|
| Selected steps | 1,768 | 1 |
| Pauli exponentials per step | 120 | 119 |
| Single-qubit gates per compiled step, before | 1,192 | 503 |
| CX gates per compiled step, before | 932 | 528 |
| Single-qubit gates per compiled step, after | 226 | 350 |
| CX gates per compiled step, after | 794 | 398 |
| Full-circuit total gates, after | 1,803,360 | 748 |

QBlue's exported production block reproduces the CSV counts exactly when multiplied
by 1,768. OpenFermion's rerun reproduces its before/after CSV counts exactly.
QBlue's 1,020 versus OpenFermion's 748 gates per step is NOT a controlled compiler
comparison: rotation angles, order, routing, and optimization scope differ.

## Where they diverge

1. **Step selection.** QBlue uses a term-count-only formula, yielding 1,768 steps.
   OpenFermion uses the tight leading-order commutator coefficient
   B=0.07683143082145469, predicting error 0.03722302053264136 at one step.
   Its method is an estimate omitting the higher-order remainder. QBlue's step
   formula assumes a unit term-norm scale but does not incorporate coefficients;
   this input has coefficients exceeding one, so its guarantee must not be inferred
   solely from the formula's comments.
2. **Order.** QBlue uses reverse file order followed by file order. OpenFermion
   uses sorted sparse Pauli tuples followed by their reverse. OpenFermion merges
   the two central equal half-rotations, giving 119 rather than 120 exponentials.
3. **Connectivity.** QBlue routes to an eight-qubit nearest-neighbor ring and
   decomposes swaps. OpenFermion's benchmark gives Qiskit no coupling map.
4. **Optimization scope.** QBlue processes the two halves through its chunked
   routing/VOQC pipeline separately, then reports block counts multiplied by r.
   OpenFermion constructs the full circuit and optimizes it with Qiskit level 3.
   Routing and optimizing QBlue's whole block together changes the counts to
   213 single-qubit and 756 CX gates; that diagnostic is not the production pipeline.
5. **Confirmed QBlue synthesis defect.** In `coq/QBlueSynthDigital.v:42`, the
   recursion tests Pauli index `m` but emits a CX using `curbit` (m+1). The initial
   call has `curbit=tarbit`, producing self-CNOTs for many terms. The production
   pre-optimization block contains 124 self-CNOTs. Qiskit refuses to load it.
   The same defect is present in the extracted, built library used in this audit.

Minimal extracted-library reproduction for exp(-i 0.1 Z0 Z1):

```qasm
cx q[1],q[1];
u1(0.20000000000000001) q[1];
cx q[1],q[1];
```

The required parity controls are qubit 0 to qubit 1. Removing self-CNOTs is not a
valid repair: it would still omit the required two-qubit parity computation.
The optimized block contains no self-CNOTs, but that does not validate optimization
of an invalid input circuit.

## Numerical accuracy check (256 × 256 matrices)

Reference: exp(-i t H). Errors below are spectral/operator norms, computed in
floating point, not formal certificates. Ideal blocks use analytic Pauli
exponentials. Qubit-string orientation is matched to the parsers (leftmost character
is qubit 0). The actual OpenFermion circuit agrees with its ideal product to ~2e-14.

| Circuit/formula | Steps | Operator-norm error |
|---|---:|---:|
| Actual OpenFermion circuit, sorted order | 1 | 0.0152136733 |
| Ideal product in QBlue order | 1 | 0.0311196883 |
| Ideal product in QBlue order | 1,768 | 9.99265e-9 |
| Ideal product in OpenFermion order | 1,768 | 4.78945e-9 |

OpenFermion using QBlue's order also gives error 0.0311196883, with 331 single-qubit
and 508 CX gates after optimization (839 total). This isolates order within the
OpenFermion pipeline; it does not repair or validate QBlue.

The ideal QBlue-order values are NOT measured errors of QBlue's compiled output.
The audit also records direct comparisons of the optimized routed block in audit.json;
those are near 2 but do not correct output layout, so they are not used as an
accuracy conclusion. The invalid self-CNOT reproduction alone is decisive.

## Conclusion

One ideal second-order step suffices numerically for either ordering on this input.
Most of the reported gate-count gap comes from 1,768 versus one selected step.
However, the QBlue synthesis defect must be resolved before a meaningful gate-cost
comparison. Then align ordering, step count, connectivity, and optimization scope.
No production compiler code, benchmark metrics, or source result CSVs were changed.

## Audit artifacts

- `audit.json`: numerical results and reproduced OpenFermion counts.
- `export_qblue.ml`: calls the existing built extracted library and exports blocks.
- `analyze.py`: reconstructs ideal products, checks exact evolution, reruns OpenFermion.
- `qblue_actual_before.qasm`, `qblue_actual_after.qasm`: production block exports.
- `qblue_minimal_ZZ.qasm`: minimal reproduction of the invalid CNOT.
- `qblue_step*.qasm`: whole-block diagnostics, distinct from chunked production.
