Require Import QuantumLib.Matrix.
From SQIR Require Import SQIR UnitaryOps UnitarySem.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.


(* Correctness for XZ =  H CNOT (IZ) CNOT H
n: # of bits; tarbit: CNOT's tarbit for collecting parity;
ul: converting gates *)
Lemma digital_ibm_correctness: forall (n tarbit : nat) (f : nat -> paulimat)
  (ul : base_ucom n) (mat : Square (2^n)),
  (n > 0) % nat
  -> ul = helper_digital_ibm_ulist n (n-1%nat) tarbit f
  -> mat = uc_eval (useq (useq ul (SQIR.Z tarbit)) (invert ul))
  -> lowprogten2mat C1 n f = mat. 
Proof.
  intros n tarbit f ul mat H0 H1.
  induction n as [ | n IHn].
  - easy.
  - simpl in *.
    admit.
Admitted.



Theorem synth_digital_ibm_correctness: forall (t : R) (n : nat) (f : nat->paulimat) 
  (mat1 mat2 : Square (2^n)),
  (n > 0) % nat
  -> mat1 = expH (2^n) t (lowprogten2mat C1 n f)
  -> mat2 = uc_eval (synth_digital_ibm_apauli t n f)
  -> mat1 = mat2.
Proof.
  intros t n f mat1 mat2 H0 H1 H2.
  destruct n as [| n].
  - easy.
  - set (ul := helper_digital_ibm_ulist (S n) (n%nat) 0 f).
    set (mat := uc_eval (useq (useq ul (SQIR.Z 0)) (invert ul))).
    subst mat1 mat2.
    rewrite (digital_ibm_correctness (S n) 0 f ul mat).
    subst mat.
    unfold synth_digital_ibm_apauli.
    replace (helper_digital_ibm_ulist (S n) (n%nat) 0 f) with ul.
    cbn [uc_eval].
  
    assert (H1: uc_eval (invert ul) = (uc_eval ul) †).
    { rewrite (invert_correct (S n) ul). easy. }

    assert (H2: expH (2 ^ (S n)) t (uc_eval (SQIR.Z 0)) = uc_eval (Rz (QBlueUtility.R2 * t) (S n))).
    { cbv [SQIR.Z Rz U_Z]. 
      admit.
    }

    rewrite H1.
    rewrite <- H2.
    apply (expH_conj_eq_conj_expH t (2^(S n)) (uc_eval ul) (uc_eval (SQIR.Z 0))).
    admit. 

    easy. easy.
    simpl. rewrite Nat.sub_0_r. easy.
    easy.
Admitted.



