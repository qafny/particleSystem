"""The openfermion synthesis path used by jbg/202603."""

import sys
from benchmark import ROOT, ParsedHamiltonian, run

sys.path.insert(0, str(ROOT / "thirdparty" / 'OpenFermion/src'))

def _build_openfermion_operator(ph: ParsedHamiltonian):
    from openfermion import QubitOperator
    op = QubitOperator()
    for label, coeff in zip(ph.paulis, ph.coeffs):
        if abs(coeff.imag) > 1e-12:
            raise ValueError(f'OpenFermion trotter baseline requires real coefficients; got {coeff!r}')
        pieces = [f'{gate}{idx}' for idx, gate in enumerate(label) if gate != 'I']
        term = ' '.join(pieces)
        op += QubitOperator(term, float(coeff.real))
    if len(op.terms) == 0:
        raise ValueError('No non-identity Hamiltonian terms remain after filtering')
    return op

def _gate_stream_to_qiskit(gate_lines: list[str], n_qubits: int):
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(n_qubits)
    for line in gate_lines:
        parts = line.split()
        if not parts:
            continue
        gate = parts[0]
        if gate == 'H':
            qc.h(int(parts[1]))
        elif gate == 'Rx':
            qc.rx(float(parts[1]), int(parts[2]))
        elif gate == 'Rz':
            qc.rz(float(parts[1]), int(parts[2]))
        elif gate == 'CNOT':
            qc.cx(int(parts[1]), int(parts[2]))
        elif gate == 'C-Phase':
            qc.cp(float(parts[1]), int(parts[2]), int(parts[3]))
        else:
            raise ValueError(f'Unsupported OpenFermion gate: {line}')
    return qc

def openfermion_compile_to_circuit(ph: ParsedHamiltonian, *, time_t: float, trotter_number: int, trotter_order: int):
    from openfermion import trotterize_exp_qubop_to_qasm
    op = _build_openfermion_operator(ph)
    gate_lines = list(trotterize_exp_qubop_to_qasm(op, evolution_time=float(time_t), trotter_number=int(trotter_number), trotter_order=int(trotter_order)))
    qc = _gate_stream_to_qiskit(gate_lines, ph.n_qubits)
    return (qc, {'qasm_gate_count': len(gate_lines)})

def compile_step(hamiltonian, time_value):
    return openfermion_compile_to_circuit(hamiltonian, time_t=time_value, trotter_number=1, trotter_order=1)[0]


if __name__ == "__main__":
    raise SystemExit(run("openfermion", compile_step, None))
