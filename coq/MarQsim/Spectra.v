From Coq Require Import String.
Require Import Marqsim.

Record SpectraArgs : Type := {
  exp_path : string;
  file_name : string
}.

Definition run_spectra (args : SpectraArgs) : nat :=
  spectra_operation (file_name args) (exp_path args).
