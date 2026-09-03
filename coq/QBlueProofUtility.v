(* Utilities for proving, not to be extracted to ocaml *)
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueSyntax.


(* L2-norm of a n*n matrix  *)
Parameter norm : forall n : nat, Square n -> R.

(* exp(-i t H) *)
Parameter expH : forall n : nat, R -> Square n -> Square n.

Axiom WF_expH : forall (n : nat) (t : R) (M : Square n), WF_Matrix (expH n t M).
Global Hint Resolve WF_expH : wf_db.

(* expH is meant to model exp(-itM), the simulation of a Hamiltonian -- and the
   whole premise of Hamiltonian simulation is that this is always unitary
   (Section 1 of the paper: "exponentiated Hamiltonians yield unitary
   operators"). Since expH is an abstract Parameter with no concrete
   definition, this foundational property has to be axiomatized rather than
   proved, same as WF_expH above. NOTE: this is stated unconditionally on M
   (not "M Hermitian implies ..."), because lowprog_ten's amplitude is typed
   as an unrestricted C rather than being statically constrained to be real
   -- so a Hermitian-conditioned version would need that extra invariant
   threaded through every caller. If that invariant ever gets added to the
   syntax/type system, this axiom should be tightened to require it. *)
Axiom expH_unitary : forall (n : nat) (t : R) (M : Square n),
  Mmult (expH n t M) ((expH n t M) †) = I n.

(* expH models exp(-itM); simulating for t1 then t2 (same generator) is the
   same as simulating for t1+t2 -- the semigroup property of time evolution.
   Foundational property of the abstract primitive, same status as
   WF_expH/expH_unitary. *)
Axiom expH_add : forall (n : nat) (t1 t2 : R) (M : Square n),
  Mmult (expH n t1 M) (expH n t2 M) = expH n (t1 + t2) M.

Lemma expH_double : forall n t M, Mmult (expH n t M) (expH n t M) = expH n (2*t) M.
Proof.
  intros. rewrite expH_add. f_equal. ring.
Qed.

(*********** Transform lowprog into Matrix. Needed for proving Hermitian **************)
Definition pauli2mat (p : paulimat) : Square 2 :=
  match p with
  | paulix => σx 
  | pauliy => σy
  | pauliz => σz 
  | paulii => I 2 
  end.

Lemma WF_pauli2mat : forall p : paulimat, WF_Matrix (pauli2mat p).
Proof.
  intro p; destruct p.
  - show_wf.
  - show_wf.
  - show_wf.
  - apply WF_I.
Qed.
Global Hint Resolve WF_pauli2mat : wf_db.

(* get exp(-i t H) from t, H.
n: # of paulimat in one pauli string *)  
Fixpoint lowprogten2mat (amp : C) (n : nat) (f: nat->paulimat) : Matrix (2^n) (2^n) :=
  match n with
  | 0 => scale amp (I (1 % nat))
  | S n' => kron (pauli2mat (f n')) (lowprogten2mat amp n' f)
  end.

Lemma wf_lowprogten2mat :
  forall (amp : C) (n : nat) (f : nat -> paulimat),
    WF_Matrix (lowprogten2mat amp n f).
Proof.
  intros amp n f.
  induction n as [| n' IH].
  - simpl. auto with wf_db. 
  - simpl.
    apply WF_kron; auto with wf_db.
Qed.
Global Hint Resolve wf_lowprogten2mat : wf_db.

Fixpoint lowprog2mat (ham : lowprog) (n : nat) : Matrix (2^n) (2^n) :=
  match ham with
  | [] => Zero
  | (amp, _, f) :: hx =>
      Mplus (lowprogten2mat amp n f) (lowprog2mat hx n)
  end.

Lemma wf_lowprog2mat :
  forall (lp : lowprog) (n : nat),
    WF_Matrix (lowprog2mat lp n).
Proof.
  intros lp n.
  induction lp as [| [[amp k] f] lpx IH].
  - simpl. apply WF_Zero.
  - simpl.
    apply WF_plus; auto with wf_db.
Qed.
Global Hint Resolve wf_lowprog2mat : wf_db.

(* lowprog2mat folds the term list via matrix sum (Mplus), which is
   commutative/associative -- so it's invariant under list order, in
   particular under reversal. *)
Lemma lowprog2mat_app : forall l1 l2 d,
  lowprog2mat (l1 ++ l2) d = Mplus (lowprog2mat l1 d) (lowprog2mat l2 d).
Proof.
  induction l1 as [| [[amp k] f] l1' IH]; intros l2 d.
  - simpl. rewrite Mplus_0_l; auto with wf_db.
  - simpl. rewrite IH. rewrite Mplus_assoc. reflexivity.
Qed.

Lemma lowprog2mat_rev : forall l d, lowprog2mat (rev l) d = lowprog2mat l d.
Proof.
  induction l as [| [[amp k] f] l' IH]; intros d.
  - reflexivity.
  - simpl. rewrite lowprog2mat_app. simpl.
    rewrite Mplus_0_r; auto with wf_db.
    rewrite IH. apply Mplus_comm.
Qed.

Definition is_hermitian_mat {n : nat} (M : Matrix n n) : Prop :=
  M † = M.

Definition is_hermitian_lowprog (H : lowprog) (n : nat) : Prop :=
  is_hermitian_mat (lowprog2mat H n).

Lemma WF_opp : forall {m n} (A : Matrix m n), WF_Matrix A -> WF_Matrix (Mopp A).
Proof.
  intros m n A H. unfold Mopp. auto with wf_db.
Qed.
Global Hint Resolve WF_opp : wf_db.

(*********** Transform lowprog into Matrix. **************)

Axiom expH_conj_eq_conj_expH: forall (t : R) (k : nat) (U P : Square k),
  Mmult (U †) U = I k
  -> expH k t (Mmult (U †) (Mmult P U) ) = Mmult (U †) (Mmult (expH k t P) U).
