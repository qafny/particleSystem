## Directory Contents

- qbluelib : The extracted ocaml code from coq.

- parser : parse the high / low level user-input hamiltonian.

- analyze\_utility.ml : translate hamiltonians into circuits, optimize gate counts.

- performance.ml : CLI entry.


## Setup

1. if you have not extracted coq yet, go to extract\_coq/README.md.

2. copy extracted code to qbluelib, run ```cp -r ../extract\_coq/ml qbluelib```

3. compile, run ```dune build```

4. run performance: ```dune exec -- ./performance.exe <file/path> [-e <float>] [-t <float>]```

- the first argument can be a txt-format file containing hamiltonian, it will translate this hamiltonian and print out the results; 
	or a directory containing these files, it will generate the txt-format file named "result_*" at the same level of the input directory.

- flag `-e`, followed by the input error for the hamiltonian translation. If not set, the default error is 1.0.

- flag `-t`, followed by the input phase `t` in `exp(-itH)`. If not set, the default error is 0.01.



