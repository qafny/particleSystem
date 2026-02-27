# QBlue Compiler
To compile QBlue, you will need [Coq](https://coq.inria.fr/). We recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.16**.


## Environment Setup
```
# initialize opam
opam init -a  

# create a switch named qblue and import the environment
opam switch create qblue
opam switch import opam-switch.export

# check if the switch and packages are right
opam switch
opam list

# install python3 for running networks
install python3.9
pip install networkx[default]

```



## Compile & Running QBlue
1. Generate Makefile if it is the first time, run `coq_makefile -f _CoqProject -o Makefile`.

2. Compile, run `make` in the current directory. 


## Directory Contents

* QBlueSyntax.v - The QBlue language syntax.
* QBlueType.v - The QBlue type system and equational theories and the dag canonical form proof.
* QBlueSemantics.v - The QBlue language semantics.
* QBlueCompiler.v - The QBlue compiler flow with different pipelines composed of different algorithms.
* QBlueParTransJwt.v - Jordan Wigner Transformation from translating high level hamiltonian to Pauli strings.
* QBlueTrotter.v - Standard Trotterization.
* QBlueQdrift.v - QDrift algorithm.
* QBlueSynthDigital.v - Decompose onto digital gates.
* QBlueSynth.v - Decompose onto analog gates.


