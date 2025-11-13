# QBlue

## Setup

To compile QBlue, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.13**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "qnp"
opam switch create qnp 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.12. We have tested compilation with 8.12.2, 8.13.2, and 8.14.0.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running QBlue

Run `make` in the top-level directory to compile our Coq proofs.

## Directory Contents

* QBlueSyntax.v - The QBlue language syntax.
* QBlueType.v - The QBlue type system and equational theories and the dag canonical form proof.
* QBlueSemantics.v - The QBlue language semantics and type soundness proofs.
* QBlueCompiler.v - The QBlue compiler and the step by step proofs in Sec.5.


## Run experiments
After Run `make` in the top-level directory to compile our Coq proofs;
Follow experiment/README.md

