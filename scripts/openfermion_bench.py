"""OpenFermion baseline: one first- or second-order Trotter step from
trotterize_exp_qubop_to_qasm, with the file's term order."""

from benchmark import ParsedHamiltonian, run


def _build_openfermion_operator(ph: ParsedHamiltonian):
    from openfermion import QubitOperator
    op = QubitOperator()
    for label, coeff in zip(ph.paulis, ph.coeffs):
        if abs(coeff.imag) > 1e-12:
            raise ValueError(f'OpenFermion trotter baseline requires real coefficients; got {coeff!r}')
        term = ' '.join(f'{gate}{idx}' for idx, gate in enumerate(label) if gate != 'I')
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


def compile_step(hamiltonian, step_time, order):
    from openfermion import trotterize_exp_qubop_to_qasm
    op = _build_openfermion_operator(hamiltonian)
    ordering = list(op.terms)  # keep the file's term order
    gate_lines = list(trotterize_exp_qubop_to_qasm(
        op, evolution_time=float(step_time), trotter_number=1, trotter_order=order, term_ordering=ordering))
    return _gate_stream_to_qiskit(gate_lines, hamiltonian.n_qubits)


if __name__ == "__main__":
    raise SystemExit(run("openfermion", compile_step, None))
