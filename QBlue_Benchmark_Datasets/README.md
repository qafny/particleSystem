## QBlue Benchmark Datasets

This directory contains benchmark datasets of qubit Hamiltonians expressed as sums of Pauli strings.
The datasets include molecular Hamiltonians generated under different fermion-to-qubit mappings
(e.g., Jordan–Wigner and Bravyi–Kitaev) and are used for benchmarking Hamiltonian simulation
and synthesis pipelines.

These Hamiltonians can be generated using **Qiskit Nature**, starting from second-quantized
electronic structure problems and mapping them to qubit operators.


NOTE: for the Genesis_dataset, you can use the following command to generate the format recognizable by our project,  
`python3 convert_pauli_txt_format.py benzene benzene_converted`

