(*
  QBlueHamiltonian.v

  Constructive matrix semantics for QBlue Pauli-string Hamiltonians.

  No Axiom.
  No Admitted.
*)

From Coq Require Import Reals List Psatz.

Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueMatNorm.

Local Open Scope R_scope.


(* ================================================================ *)
(* 1. Pauli matrices                                                *)
(* ================================================================ *)

Definition pauli2mat (p : paulimat) : Square 2 :=
  match p with
  | paulix => σx
  | pauliy => σy
  | pauliz => σz
  | paulii => I 2
  end.

Lemma WF_pauli2mat :
  forall p : paulimat,
    WF_Matrix (pauli2mat p).
Proof.
  intro p.
  destruct p.
  - show_wf.
  - show_wf.
  - show_wf.
  - apply WF_I.
Qed.

Global Hint Resolve WF_pauli2mat : wf_db.


(* ================================================================ *)
(* 2. Pauli-string matrices                                         *)
(* ================================================================ *)

Fixpoint lowprogten2mat
  (amp : C) (n : nat) (f : nat -> paulimat)
  : Matrix (2^n) (2^n) :=
  match n with
  | 0 =>
      scale amp (I 1)
  | S n' =>
      kron
        (pauli2mat (f n'))
        (lowprogten2mat amp n' f)
  end.

Lemma wf_lowprogten2mat :
  forall (amp : C) (n : nat) (f : nat -> paulimat),
    WF_Matrix (lowprogten2mat amp n f).
Proof.
  intros amp n f.
  induction n as [| n' IH].
  - simpl.
    auto with wf_db.
  - simpl.
    apply WF_kron; auto with wf_db.
Qed.

Global Hint Resolve wf_lowprogten2mat : wf_db.


(* ================================================================ *)
(* 3. Real-amplitude Hamiltonian terms                              *)
(* ================================================================ *)

Definition normten2mat
  (amp : R) (n : nat) (f : nat -> paulimat)
  : Matrix (2^n) (2^n) :=
  lowprogten2mat (RtoC amp) n f.

Lemma wf_normten2mat :
  forall (amp : R) (n : nat) (f : nat -> paulimat),
    WF_Matrix (normten2mat amp n f).
Proof.
  intros.
  unfold normten2mat.
  auto with wf_db.
Qed.

Global Hint Resolve wf_normten2mat : wf_db.


(* ================================================================ *)
(* 4. Hamiltonian programs                                          *)
(* ================================================================ *)

Fixpoint norm_prog2mat
  (np : norm_prog) (n : nat)
  : Matrix (2^n) (2^n) :=
  match np with
  | [] =>
      Zero
  | (amp, f) :: nx =>
      Mplus
        (normten2mat amp n f)
        (norm_prog2mat nx n)
  end.

Lemma wf_norm_prog2mat :
  forall (np : norm_prog) (n : nat),
    WF_Matrix (norm_prog2mat np n).
Proof.
  induction np as [| [amp f] nx IH]; intros n.
  - simpl.
    apply WF_Zero.
  - simpl.
    apply WF_plus; auto with wf_db.
Qed.

Global Hint Resolve wf_norm_prog2mat : wf_db.


Lemma norm_prog2mat_app :
  forall l1 l2 d,
    norm_prog2mat (l1 ++ l2) d
    =
    Mplus (norm_prog2mat l1 d)
          (norm_prog2mat l2 d).
Proof.
  induction l1 as [| [amp f] l1' IH]; intros l2 d.
  - simpl.
    rewrite Mplus_0_l; auto with wf_db.
  - simpl.
    rewrite IH.
    rewrite Mplus_assoc.
    reflexivity.
Qed.


Lemma norm_prog2mat_rev :
  forall l d,
    norm_prog2mat (rev l) d = norm_prog2mat l d.
Proof.
  induction l as [| [amp f] l' IH]; intros d.
  - reflexivity.
  - simpl.
    rewrite norm_prog2mat_app.
    simpl.
    rewrite Mplus_0_r; auto with wf_db.
    rewrite IH.
    apply Mplus_comm.
Qed.


(* ================================================================ *)
(* 5. Hermiticity                                                   *)
(* ================================================================ *)

Definition is_hermitian_mat {n : nat}
  (M : Matrix n n) : Prop :=
  M † = M.


Lemma Cconj_RtoC :
  forall r : R,
    Cconj (RtoC r) = RtoC r.
Proof.
  intros r.
  lca.
Qed.


Lemma scale_adjoint :
  forall {m n} (c : C) (A : Matrix m n),
    (scale c A) † =
    scale (Cconj c) (A †).
Proof.
  intros m n c A.
  unfold adjoint, scale.
  prep_matrix_equality.
  apply Cconj_mult_distr.
Qed.


Lemma hermitian_pauli2mat :
  forall p,
    is_hermitian_mat (pauli2mat p).
Proof.
  intros p.
  unfold is_hermitian_mat.
  destruct p; simpl.
  - exact σx_hermitian.
  - exact σy_hermitian.
  - exact σz_hermitian.
  - exact I_hermitian.
Qed.


Lemma hermitian_normten :
  forall amp n f,
    is_hermitian_mat (normten2mat amp n f).
Proof.
  intros amp n f.
  unfold normten2mat, is_hermitian_mat.
  induction n as [| n' IH].

  - simpl.
    rewrite scale_adjoint.
    rewrite Cconj_RtoC.
    rewrite id_adjoint_eq.
    reflexivity.

  - cbn [lowprogten2mat].
    transitivity
      (kron
         ((pauli2mat (f n')) †)
         ((lowprogten2mat amp n' f) †)).
    + apply kron_adjoint.
    + rewrite IH.
      rewrite (hermitian_pauli2mat (f n')).
      reflexivity.
Qed.


Lemma hermitian_norm_prog2mat :
  forall np n,
    is_hermitian_mat (norm_prog2mat np n).
Proof.
  induction np as [| [amp f] nx IH]; intros n.

  - unfold is_hermitian_mat.
    simpl.
    apply zero_adjoint_eq.

  - unfold is_hermitian_mat in *.
    simpl.
    rewrite Mplus_adjoint.
    rewrite (hermitian_normten amp n f).
    rewrite IH.
    reflexivity.
Qed.

