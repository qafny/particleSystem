Require Import QuantumLib.Matrix.
From SQIR Require Import SQIR.
From SQIR Require Import UnitarySem.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.


Definition denote (t : R) (n : nat) (lp : lowprog) : Square (2^n) :=
  Zero.



Theorem synth_digital_ibm_correctness: forall (t : R) (n : nat) (lp : lowprog) (mat1 mat2 : Square (2^n)),
  mat1 = denote t n lp
  -> mat2 = uc_eval (synth_digital_ibm t n lp)
  -> mat1 == mat2.
Proof.
Admitted.

