Require Import QuantumLib.Matrix.
From SQIR Require Import SQIR UnitaryOps UnitarySem.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.


Definition denote (n : nat) (f : nat -> paulimat) : Square (2^n) :=
  Zero.


(* Correctness for XZ =  H CNOT (IZ) CNOT H
n: # of bits; tarbit: CNOT's tarbit for collecting parity;
ul: converting gates *)
Lemma digital_ibm_correctness: forall (n tarbit : nat) (f : nat -> paulimat)
  (ul : base_ucom n) (mat : Square (2^n)),
  ul = helper_digital_ibm_ulist n 0 tarbit f
  -> mat = uc_eval (useq (useq ul (Z tarbit)) (invert ul))
  -> denote n f = mat. 
Proof.
Admitted.



Theorem synth_digital_ibm_correctness: forall (t : R) (n : nat) (f : nat->paulimat) 
  (mat1 mat2 : Square (2^n)),
  mat1 = expH (2^n) t (denote n f)
  -> mat2 = uc_eval (synth_digital_ibm_apauli t n f)
  -> mat1 = mat2.
Proof.
  intros t n f mat1 mat2 H0 H1.
  set (ul := helper_digital_ibm_ulist n 0 0 f).
  set (mat := uc_eval (useq (useq ul (Z 0)) (invert ul))).
  subst mat1 mat2.
  rewrite (digital_ibm_correctness n 0 f ul mat).
  subst mat.
  unfold synth_digital_ibm_apauli.
  replace (helper_digital_ibm_ulist n 0 0 f) with ul.
  cbn [uc_eval].
 
  assert (H1: uc_eval (invert ul) = (uc_eval ul) †).
  { rewrite (invert_correct n ul). easy. }

  assert (H2: expH (2 ^ n) t (uc_eval (Z 0)) = uc_eval (Rz (QBlueUtility.R2 * t) n)).
  { cbv [Z Rz U_Z]. 
    admit.
  }

  rewrite H1.
  rewrite <- H2.
  apply (expH_conj_eq_conj_expH t (2^n) (uc_eval ul) (uc_eval (Z 0))).
  admit. 

  easy. easy. easy.
Admitted.



