## Directory Contents

- qbluelib : The extracted ocaml code from coq.

- parser : parse the high / low level user-input hamiltonian.

- analyze\_utility.ml : translate hamiltonians into circuits, optimize gate counts.

- performance.ml : CLI entry.


## Setup

1. if you have not extracted coq yet, go to extract\_coq/README.md.

2. copy extracted code to qbluelib, run ```cp -r ../extract\_coq/ml qbluelib```

3. compile, run ```dune build```

4. run performance: ```dune exec -- ./performance.exe <file/path> [-e <float>] [-t <float>] [-o <string>]```

- the first argument can be a txt-format file containing hamiltonian, it will translate this hamiltonian and print out the results; 
	or a directory containing these files, it will generate the txt-format file named by the -o flag in the current directory.

- flag `-e`, followed by the input error for the hamiltonian translation. If not set, the default error is 1.0.

- flag `-t`, followed by the input phase `t` in `exp(-itH)`. If not set, the default error is 0.01.

- flag `-p`, followed by the path flag to control which algorithm to use for compilation. If not set, default is 0 (optimal CNOT gate counts path). Options include 0-4 (digital) and 10-14 (Indiana Analog)

- flag `-o`, deprecated. followed by the input string to save the results. USE THIS ONLY WHEN input is a directory. If not set, the default error is `result.txt`.


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



