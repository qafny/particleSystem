"""Phoenix baseline (DAC'25 PHOENIX, phoenix-quantum with grouping="support").

Phoenix compiles exp(-i sum_j c_j P_j) as a product of Pauli exponentials in an
order of its choosing, so one first-order step uses coefficients h_j * dt. A
second-order step is S1(dt/2) followed by the reversed product, built as the
inverse of the circuit for -dt/2.
"""

from benchmark import run


def _compile(hamiltonian, scale):
    import phoenix
    # Qiskit labels are little-endian; the input files put qubit 0 first.
    labels = [label[::-1] for label in hamiltonian.paulis]
    coeffs = [coeff.real * scale for coeff in hamiltonian.coeffs]
    return phoenix.compile_hamiltonian_simulation(phoenix.Hamiltonian(labels, coeffs), grouping="support")


def compile_step(hamiltonian, step_time, order):
    if order == 1:
        return _compile(hamiltonian, step_time)
    half = _compile(hamiltonian, step_time / 2)
    return half.compose(_compile(hamiltonian, -step_time / 2).inverse())


if __name__ == "__main__":
    raise SystemExit(run("phoenix", compile_step, None))
