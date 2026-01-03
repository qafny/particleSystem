(* Utilities for proving, not to be extracted to ocaml *)
Require Import QuantumLib.Matrix.


(* L2-norm of a n*n matrix  *)
Parameter norm : forall n : nat, Square n -> R.

(* exp(-i t H) *)
Parameter expH : forall n : nat, R -> Square n -> Square n.


Theorem expH_conj_eq_conj_expH: forall (t : R) (k : nat) (U P : Square k),
  Mmult (U †) U = I k
  -> expH k t (Mmult (U †) (Mmult P U) ) = Mmult (U †) (Mmult (expH k t P) U).
Proof.
Admitted.
