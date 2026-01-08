(* Utilities for proving, not to be extracted to ocaml *)
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueSyntax.


(* L2-norm of a n*n matrix  *)
Parameter norm : forall n : nat, Square n -> R.

(* exp(-i t H) *)
Parameter expH : forall n : nat, R -> Square n -> Square n.


(*********** Transform lowprog into Matrix. Needed for proving Hermitian **************)
Definition pauli2mat (p : paulimat) : Square 2 :=
  match p with
  | paulix => σx 
  | pauliy => σy
  | pauliz => σz 
  | paulii => I 2 
  end.

(* get exp(-i t H) from t, H.
n: # of paulimat in one pauli string *)  
Fixpoint lowprogten2mat (amp : C) (n : nat) (f: nat->paulimat) : Matrix (2^n) (2^n) :=
  match n with
  | 0 => scale amp (I (1 % nat))
  | S n' => kron (pauli2mat (f n')) (lowprogten2mat amp n' f)
  end.

Fixpoint lowprog2mat (ham : lowprog) (n : nat) : Matrix (2^n) (2^n) :=
  match ham with
  | [] => Zero
  | (amp, _, f) :: hx =>
      Mplus (lowprogten2mat amp n f) (lowprog2mat hx n)
  end.

Definition is_hermitian_mat {n : nat} (M : Matrix n n) : Prop :=
  M † = M.

Definition is_hermitian_lowprog (H : lowprog) (n : nat) : Prop :=
  is_hermitian_mat (lowprog2mat H n).
(*
Record HermitianLowprog := {
  Hlp        : lowprog;
  Hlp_hermitian : is_hermitian_lowprog Hlp;
}. *)

(*********** Transform lowprog into Matrix. **************)



Theorem expH_conj_eq_conj_expH: forall (t : R) (k : nat) (U P : Square k),
  Mmult (U †) U = I k
  -> expH k t (Mmult (U †) (Mmult P U) ) = Mmult (U †) (Mmult (expH k t P) U).
Proof.
Admitted.
