#!/usr/bin/env python3

import sys

if len(sys.argv) != 2:
    print("usage: ./simulate-qasm.py test.qasm")
    exit(0)

import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.providers.aer import QasmSimulator
from qiskit.visualization import plot_histogram

simulator = QasmSimulator()
circuit = QuantumCircuit.from_qasm_file(sys.argv[1])

# I have a feeling this isn't necessary for the QASM we generate
compiled_circuit = transpile(circuit, simulator)

# Execute the circuit on the qasm simulator
job = simulator.run(compiled_circuit, shots=1000)
result = job.result()
counts = result.get_counts(compiled_circuit)
print(counts)
