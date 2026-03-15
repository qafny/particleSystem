## Directory Contents

- qbluelib : The extracted ocaml code from coq.

- parser : parse the high / low level user-input hamiltonian.

- analyze\_utility.ml : translate hamiltonians into circuits, optimize gate counts.

- performance.ml : CLI entry.


## Setup

1. if you have not extracted coq yet, go to extract\_coq/README.md.

2. copy extracted code to qbluelib, run ```cp -r ../extract\_coq/ml qbluelib```

3. compile, run ```dune build```

4. run performance: `dune exec -- ./performance.exe <file/path> [-e <float>] [-t <float>] [-p <int>]`

- the first argument should be a txt-format file containing a Hamiltonian. The program prints JSON results to `stdout`.

- flag `-e`, followed by the input error for the hamiltonian translation. If not set, the default error is 1.0.

- flag `-t`, followed by the input phase `t` in `exp(-itH)`. If not set, the default error is 0.01.

- flag `-p`, followed by the path flag to control which algorithm to use for compilation. If not set, default is 0.
  1. Trotterization (1st-order) -> IBMDigital circuits
  2. Trotterization (2nd-order) -> IBMDigital circuits
  3. qdrift -> IBMDigital circuits 
  4. MarQSim (CNOT for P_gc) -> IBMDigital circuits
  5. MarQSim (CNOT+SingleQ for P_gc) -> IBMDigital circuits
  6. MarQSim (CNOT for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> IBMDigital circuits
  7. MarQSim (CNOT+SingleQ for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> IBMDigital circuits
  0. Optimal among 0-7
  11. Trotterization (1st-order) -> Indiana Analog circuits
  12. Trotterization (2nd-order) -> Indiana Analog circuits
  13. qdrift -> Indiana Analog circuits
  14. MarQSim (CNOT for P_gc) -> Indiana Analog circuits
  15. MarQSim (CNOT+SingleQ for P_gc) -> Indiana Analog circuits
  16. MarQSim (CNOT for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> Indiana Analog circuits
  17. MarQSim (CNOT+SingleQ for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> Indiana Analog circuits
  10. Optimal among 10-17
  21. Trotterization (1st-order) -> IBM Analog circuits
  22. Trotterization (2nd-order) -> IBM Analog circuits
  23. qdrift -> IBM Analog circuits
  24. MarQSim (CNOT for P_gc) -> IBM Analog circuits
  25. MarQSim (CNOT+SingleQ for P_gc) -> IBM Analog circuits
  26. MarQSim (CNOT for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> IBM Analog circuits
  27. MarQSim (CNOT+SingleQ for P_gc; 0.6 P_gc + 0.4 P_qdrift) -> IBM Analog circuits
  20. Optimal among 20-27





## DataSet
Those from Genesis Dataset:
JW_* : Jordan-Wigner transform
BK_* : Bravyi-Kitaev transform

Those from MarQSim Dataset
MarqSim_*


Those from adaptvqite_work:
  - GImpModels: impurity-model input generation and analysis.
      - Builds HEmbed.h5 embedding Hamiltonians.
      - Mode subfolders (s\_imp\_mode\_B3, p\_imp\_mode\_B3, d\_imp\_mode\_B3, f\_imp\_mode\_B3) are separate orbital models.
  - TFIM1d: 1D transverse-field Ising model experiments.
      - n8, n12, n16, n20 are system sizes.
      - write\_incar.py generates Ising Hamiltonian + operator pool into incar.
  - SSH, SSH-UV, SSH-U2V0, SSH-U10V0: Su-Schrieffer-Heeger model parameter sweeps under different interaction settings.
      - N4/N6 are system sizes.
      - dt-1.0 ... dt1.0 subfolders are sweep points (likely time-step/driving parameter scans).
  - hubbardmodel: Fermi-Hubbard model setup and HPC runs.
      - create\_hubbardmidel\_incar.py uses OpenFermion (fermi\_hubbard + Jordan-Wigner) to generate incar.
      - N2, N4, N12 are lattice sizes.
      - pool-1, pool-full, pool-test* are operator-pool variants/experiments.
      - job.slurm files run ADAPT-VQITE via MPI on cluster nodes.
      - configs/ holds cotengra optimizer configs.
  - molecules: small molecular benchmarks.
      - mol.py builds qubit Hamiltonians with Qiskit Nature (PySCF + freeze core), creates pool/reference, writes incar.
      - Example case: N2/b1.1 with geometry in inp.py.
  - Fragments: larger molecular/fragment workflows.
      - Similar pipeline to molecules, with cases like ZSM\_C2H4/36.
      - Includes its own environment lockfile (requirements.txt) for heavier chemistry stack.

## run experiments
`python3 gen\_result.py -i job.csv -o result.cvs`
