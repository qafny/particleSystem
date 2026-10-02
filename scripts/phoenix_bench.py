"""The phoenix synthesis path used by jbg/202603."""

import sys
from benchmark import ROOT, ParsedHamiltonian, run

sys.path.insert(0, str(ROOT / "thirdparty" / 'phoenix'))

def _optimize_phoenix_circuit_by_qiskit(qc):
    from itertools import product
    from qiskit.transpiler import PassManager, passes
    from phoenix.basics import CNOTEquivCliffordGate
    inverse_list = [CNOTEquivCliffordGate(p0, p1) for p0, p1 in product(['x', 'y', 'z'], repeat=2)]
    pm = PassManager()
    pm.append(passes.InverseCancellation(inverse_list))
    pm.append(passes.CommutativeInverseCancellation(matrix_based=True))
    pm.append(passes.Optimize1qGatesDecomposition())
    pm.append(passes.CommutativeCancellation())
    return pm.run(qc)

def phoenix_compile_to_circuit(ph: ParsedHamiltonian, *, time_t: float, order_method: str):
    import numpy as np
    from phoenix.hamiltonian import Hamiltonian
    from phoenix.primitive.ordering import order_circuits
    from phoenix.primitive.simplification import simplify_hamiltonian
    from phoenix.primitive.utils import constr_circuit_from_simp_steps
    if not ph.paulis:
        raise ValueError('No Hamiltonian terms parsed')
    n = len(ph.paulis[0])
    if any((len(p) != n for p in ph.paulis)):
        raise ValueError('Inconsistent Pauli string lengths in input')
    coeffs = np.asarray(ph.coeffs, dtype=np.complex128) * float(time_t)
    ham = Hamiltonian(ph.paulis, coeffs)
    sub_hams = ham.group_same_weights()
    circuits = []
    for sub in sub_hams:
        sub_simplified, simp_steps = simplify_hamiltonian(sub)
        circuits.append(constr_circuit_from_simp_steps(sub_simplified, simp_steps))
    return order_circuits(circuits, method=order_method)

def compile_step(hamiltonian, time_value):
    return phoenix_compile_to_circuit(hamiltonian, time_t=time_value, order_method="trivial")


if __name__ == "__main__":
    raise SystemExit(run("phoenix", compile_step, _optimize_phoenix_circuit_by_qiskit))
