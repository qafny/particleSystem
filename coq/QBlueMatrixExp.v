(*
  QBlueMatrixExp.v

  Axiom-free finite matrix-exponential foundation for QBlue.

  Stage 1:
    - matrix powers
    - finite exponential partial sums
    - well-formedness
    - operator-norm bound on matrix powers
*)

From Coq Require Import Reals.
From Coq Require Import Psatz.
From Coq Require Import Arith.
From Coq Require Import Lia.

Require Import QuantumLib.Matrix.
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueMatNorm.

Local Open Scope R_scope.
Local Open Scope matrix_scope.


(* ================================================================ *)
(* 1. Matrix powers                                                  *)
(* ================================================================ *)

Fixpoint matrix_power {n : nat}
    (A : Square n) (k : nat) : Square n :=
  match k with
  | O    => I n
  | S k' => A × matrix_power A k'
  end.


Lemma matrix_power_0 :
  forall n (A : Square n),
    matrix_power A 0 = I n.
Proof.
  reflexivity.
Qed.


Lemma matrix_power_S :
  forall n (A : Square n) k,
    matrix_power A (S k)
    =
    A × matrix_power A k.
Proof.
  reflexivity.
Qed.


(* ================================================================ *)
(* 2. Well-formedness of matrix powers                              *)
(* ================================================================ *)

Lemma WF_matrix_power :
  forall n (A : Square n) k,
    WF_Matrix A ->
    WF_Matrix (matrix_power A k).
Proof.
  intros n A k HA.
  induction k as [| k IH].
  - simpl.
    apply WF_I.
  - simpl.
    apply WF_mult.
    + exact HA.
    + exact IH.
Qed.

Global Hint Resolve WF_matrix_power : wf_db.


(* ================================================================ *)
(* 3. Operator norm of a matrix power                               *)
(*                                                                  *)
(*       ||A^k|| <= ||A||^k                                         *)
(* ================================================================ *)

Lemma mnorm_matrix_power_le :
  forall n (A : Square n) k,
    mnorm n (matrix_power A k)
    <= (mnorm n A) ^ k.
Proof.
  intros n A k.
  induction k as [| k IH].

  - simpl.

    destruct n as [| n'].

    + rewrite mnorm_dim0.
      simpl.
      lra.

    + assert (HI :
        mnorm (S n') (I (S n')) = 1).
      {
        apply mnorm_unitary.
        - apply WF_I.
        - lia.
        - rewrite id_adjoint_eq.
          rewrite Mmult_1_l.
          + reflexivity.
          + apply WF_I.
      }

      rewrite HI.
      simpl.
      lra.

  - simpl.

    eapply Rle_trans.

    + apply mnorm_submult.

    + apply Rmult_le_compat_l.
      * apply mnorm_nonneg.
      * exact IH.
Qed.



(* ================================================================ *)
(* 4. A real scalar coefficient for 1/k!                            *)
(* ================================================================ *)

Definition inv_fact (k : nat) : R :=
  / INR (fact k).

Lemma fact_pos :
  forall k : nat,
    (0 < fact k)%nat.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma inv_fact_nonneg :
  forall k,
    0 <= inv_fact k.
Proof.
  intros k.
  unfold inv_fact.
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  apply lt_0_INR.
  apply fact_pos.
Qed.



(* ================================================================ *)
(* 5. Individual term A^k / k!                                     *)
(* ================================================================ *)

Definition matrix_exp_term {n : nat}
    (A : Square n) (k : nat) : Square n :=
  RtoC (inv_fact k) .* matrix_power A k.


Lemma WF_matrix_exp_term :
  forall n (A : Square n) k,
    WF_Matrix A ->
    WF_Matrix (matrix_exp_term A k).
Proof.
  intros n A k HA.
  unfold matrix_exp_term.
  auto with wf_db.
Qed.

Global Hint Resolve WF_matrix_exp_term : wf_db.


(* ================================================================ *)
(* 6. Finite exponential partial sum                                *)
(*                                                                  *)
(*   matrix_exp_partial A N                                         *)
(*                                                                  *)
(* represents                                                        *)
(*                                                                  *)
(*       sum_{k=0}^{N} A^k / k!                                     *)
(*                                                                  *)
(* ================================================================ *)

Fixpoint matrix_exp_partial {n : nat}
    (A : Square n) (N : nat) : Square n :=
  match N with
  | O =>
      matrix_exp_term A 0

  | S N' =>
      matrix_exp_partial A N'
      .+
      matrix_exp_term A (S N')
  end.


Lemma matrix_exp_partial_0 :
  forall n (A : Square n),
    matrix_exp_partial A 0
    =
    matrix_exp_term A 0.
Proof.
  reflexivity.
Qed.


Lemma matrix_exp_partial_S :
  forall n (A : Square n) N,
    matrix_exp_partial A (S N)
    =
    matrix_exp_partial A N
    .+
    matrix_exp_term A (S N).
Proof.
  reflexivity.
Qed.


(* ================================================================ *)
(* 7. Well-formedness of partial sums                               *)
(* ================================================================ *)

Lemma WF_matrix_exp_partial :
  forall n (A : Square n) N,
    WF_Matrix A ->
    WF_Matrix (matrix_exp_partial A N).
Proof.
  intros n A N HA.
  induction N as [| N IH].

  - simpl.
    apply WF_matrix_exp_term.
    exact HA.

  - simpl.
    apply WF_plus.
    + exact IH.
    + apply WF_matrix_exp_term.
      exact HA.
Qed.

Global Hint Resolve WF_matrix_exp_partial : wf_db.


(* ================================================================ *)
(* 8. Norm bound for one exponential-series term                    *)
(*                                                                  *)
(*    || A^k/k! || <= (1/k!) ||A||^k                               *)
(* ================================================================ *)
Lemma mnorm_matrix_exp_term_le :
  forall n (A : Square n) k,
    mnorm n (matrix_exp_term A k)
    <= inv_fact k * (mnorm n A)^k.
Proof.
  intros n A k.
  unfold matrix_exp_term.

  rewrite mnorm_scale.

  assert (Hinv : 0 <= inv_fact k).
  {
    exact (inv_fact_nonneg k).
  }

  assert (Habs : Rabs (inv_fact k) = inv_fact k).
  {
    apply Rabs_pos_eq.
    exact Hinv.
  }

  rewrite Habs.

  apply Rmult_le_compat_l.
  - exact Hinv.
  - apply mnorm_matrix_power_le.
Qed.



(* ================================================================ *)
(* 9. Norm bound for finite exponential partial sums                *)
(* ================================================================ *)

Fixpoint scalar_exp_partial (x : R) (N : nat) : R :=
  match N with
  | O =>
      inv_fact 0 * x^0

  | S N' =>
      scalar_exp_partial x N'
      +
      inv_fact (S N') * x^(S N')
  end.


Lemma scalar_exp_partial_nonneg :
  forall x N,
    0 <= x ->
    0 <= scalar_exp_partial x N.
Proof.
  intros x N Hx.
  induction N as [| N IH].

  - simpl.
    apply Rmult_le_pos.
    + apply inv_fact_nonneg.
    +lra.

  - simpl.
    apply Rplus_le_le_0_compat.
    + exact IH.
    + apply Rmult_le_pos.
      * apply inv_fact_nonneg.
      *apply Rmult_le_pos.
 exact Hx.
 apply pow_le.
  exact Hx.
Qed.


Lemma mnorm_matrix_exp_partial_le :
  forall n (A : Square n) N,
    mnorm n (matrix_exp_partial A N)
    <= scalar_exp_partial (mnorm n A) N.
Proof.
  intros n A N.
  induction N as [| N IH].

  - simpl.
    apply mnorm_matrix_exp_term_le.

  - simpl.

    eapply Rle_trans.

    + apply mnorm_triangle.

    + apply Rplus_le_compat.
      * exact IH.
      * apply mnorm_matrix_exp_term_le.
Qed.







(* ================================================================ *)
(* 10. Second-order finite remainder                                *)
(*                                                                  *)
(* For N >= 0:                                                      *)
(*                                                                  *)
(*   matrix_exp_remainder A N                                       *)
(*      = A^2/2! + A^3/3! + ... + A^(N+2)/(N+2)!                  *)
(*                                                                  *)
(* This is the part of the exponential after I + A.                 *)
(* ================================================================ *)

Fixpoint matrix_exp_remainder {n : nat}
    (A : Square n) (N : nat) : Square n :=
  match N with
  | O =>
      matrix_exp_term A 2
  | S N' =>
      matrix_exp_remainder A N'
      .+
      matrix_exp_term A (S (S (S N')))
  end.


Fixpoint scalar_exp_remainder
    (x : R) (N : nat) : R :=
  match N with
  | O =>
      inv_fact 2 * x^2
  | S N' =>
      scalar_exp_remainder x N'
      +
      inv_fact (S (S (S N'))) * x^(S (S (S N')))
  end.


(* ================================================================ *)
(* 11. Well-formedness                                              *)
(* ================================================================ *)

Lemma WF_matrix_exp_remainder :
  forall n (A : Square n) N,
    WF_Matrix A ->
    WF_Matrix (matrix_exp_remainder A N).
Proof.
  intros n A N HA.
  induction N as [| N IH].
  - simpl.
    apply WF_matrix_exp_term.
    exact HA.
  - simpl.
    apply WF_plus.
    + exact IH.
    + apply WF_matrix_exp_term.
      exact HA.
Qed.

Global Hint Resolve WF_matrix_exp_remainder : wf_db.


(* ================================================================ *)
(* 12. Scalar remainder is nonnegative                              *)
(* ================================================================ *)
Lemma scalar_exp_remainder_nonneg :
  forall x N,
    0 <= x ->
    0 <= scalar_exp_remainder x N.
Proof.
  intros x N Hx.
  induction N as [| N IH].

  - simpl.
    apply Rmult_le_pos.
    + apply inv_fact_nonneg.
    + apply Rmult_le_pos.
      * exact Hx.
      * lra.

  - simpl.
    apply Rplus_le_le_0_compat.
    + exact IH.
    + apply Rmult_le_pos.
      * apply inv_fact_nonneg.
      * apply Rmult_le_pos.
        -- exact Hx.
        -- apply Rmult_le_pos.
           ++ exact Hx.
           ++ apply Rmult_le_pos.
              ** exact Hx.
              ** apply pow_le.
                 exact Hx.
Qed.



(* ================================================================ *)
(* 13. Operator-norm bound for finite remainder                     *)
(*                                                                  *)
(*   ||R_N(A)||                                                     *)
(*      <= sum_{k=2}^{N+2} ||A||^k/k!                              *)
(* ================================================================ *)

Lemma mnorm_matrix_exp_remainder_le :
  forall n (A : Square n) N,
    mnorm n (matrix_exp_remainder A N)
    <= scalar_exp_remainder (mnorm n A) N.
Proof.
  intros n A N.
  induction N as [| N IH].

  - simpl.
    apply mnorm_matrix_exp_term_le.

  - simpl.
    eapply Rle_trans.
    + apply mnorm_triangle.
    + apply Rplus_le_compat.
      * exact IH.
      * apply mnorm_matrix_exp_term_le.
Qed.



(* ================================================================ *)
(* 14. First exponential terms are I and A                          *)
(* ================================================================ *)

Lemma inv_fact_0 :
  inv_fact 0 = 1.
Proof.
  unfold inv_fact.
  simpl.
  field.
Qed.


Lemma inv_fact_1 :
  inv_fact 1 = 1.
Proof.
  unfold inv_fact.
  simpl.
  field.
Qed.


Lemma matrix_exp_term_0 :
  forall n (A : Square n),
    matrix_exp_term A 0 = I n.
Proof.
  intros n A.
  unfold matrix_exp_term.
  rewrite inv_fact_0.
  simpl.
  rewrite Mscale_1_l.
  reflexivity.
Qed.


Lemma matrix_exp_term_1 :
  forall n (A : Square n),
    WF_Matrix A ->
    matrix_exp_term A 1 = A.
Proof.
  intros n A HA.
  unfold matrix_exp_term.
  rewrite inv_fact_1.
  simpl.

  rewrite Mmult_1_r.
  - rewrite Mscale_1_l.
    reflexivity.
  - exact HA.
Qed.


(* ================================================================ *)
(* 15. Partial exponential = I + A + second-order remainder         *)
(* ================================================================ *)

Lemma matrix_exp_partial_remainder_decomp :
  forall n (A : Square n) N,
    WF_Matrix A ->
    matrix_exp_partial A (S (S N))
    =
    (I n .+ A) .+ matrix_exp_remainder A N.
Proof.
  intros n A N HA.
  induction N as [| N IH].

  - simpl.

    rewrite matrix_exp_term_0.
    rewrite matrix_exp_term_1 by exact HA.

    reflexivity.
  - rewrite matrix_exp_partial_S.
    rewrite IH.
    cbn [matrix_exp_remainder].
    rewrite Mplus_assoc.
    reflexivity.
Qed.

(* ================================================================ *)
(* 16. Subtracting I + A leaves exactly the remainder               *)
(* ================================================================ *)
Lemma matrix_exp_partial_minus_linear :
  forall n (A : Square n) N,
    WF_Matrix A ->
    Mminus
      (matrix_exp_partial A (S (S N)))
      (I n .+ A)
    =
    matrix_exp_remainder A N.
Proof.
  intros n A N HA.

  rewrite matrix_exp_partial_remainder_decomp by exact HA.

  unfold Mminus.

  lma.
Qed.

(* ================================================================ *)
(* 17. Finite second-order matrix-exponential bound                 *)
(* ================================================================ *)

Theorem matrix_exp_partial_second_order_bound :
  forall n (A : Square n) N,
    WF_Matrix A ->
    mnorm n
      (Mminus
         (matrix_exp_partial A (S (S N)))
         (I n .+ A))
    <=
    scalar_exp_remainder (mnorm n A) N.
Proof.
  intros n A N HA.

  rewrite matrix_exp_partial_minus_linear by exact HA.

  apply mnorm_matrix_exp_remainder_le.
Qed.
(* ================================================================ *)
(* 18. Connection with Coq's real exponential series                *)
(* ================================================================ *)

Lemma scalar_exp_partial_E1 :
  forall x N,
    scalar_exp_partial x N = E1 x N.
Proof.
  intros x N.
  induction N as [| N IH].

  - unfold scalar_exp_partial.
    unfold E1.
    simpl.
    unfold inv_fact.
    reflexivity.

  - simpl [scalar_exp_partial].
    rewrite IH.
unfold inv_fact.
simpl.
reflexivity.
Qed.

(* ================================================================ *)
(* 19. Convergence of our scalar exponential partial sums            *)
(* ================================================================ *)

Theorem scalar_exp_partial_cvg :
  forall x,
    Un_cv
      (fun N => scalar_exp_partial x N)
      (exp x).
Proof.
  intros x.

  apply (Un_cv_ext
           (E1 x)
           (fun N => scalar_exp_partial x N)).

  - intro N.
    symmetry.
    apply scalar_exp_partial_E1.

  - apply E1_cvg.
Qed.

Lemma scalar_exp_partial_S :
  forall x N,
    scalar_exp_partial x (S N)
    =
    scalar_exp_partial x N
    +
    inv_fact (S N) * x^(S N).
Proof.
  reflexivity.
Qed.


Lemma scalar_exp_partial_remainder_decomp :
  forall x N,
    scalar_exp_partial x (S (S N))
    =
    1 + x + scalar_exp_remainder x N.
Proof.
  intros x N.
  induction N as [| N IH].

  - unfold scalar_exp_partial.
    unfold scalar_exp_remainder.
    unfold inv_fact.
    simpl.
    field.

  - rewrite scalar_exp_partial_S.
    rewrite IH.

    change
      (1 + x + scalar_exp_remainder x N
       + inv_fact (S (S (S N))) * x ^ (S (S (S N)))
       =
       1 + x +
       (scalar_exp_remainder x N
        + inv_fact (S (S (S N))) * x ^ (S (S (S N))))).

    ring.
Qed.

(* ================================================================ *)
(* 20. Convergence of the scalar second-order remainder             *)
(* ================================================================ *)

Lemma scalar_exp_remainder_cvg :
  forall x,
    Un_cv
      (fun N => scalar_exp_remainder x N)
      (exp x - 1 - x).
Proof.
  intros x.

  pose proof (scalar_exp_partial_cvg x) as Hcvg.

  unfold Un_cv in Hcvg |- *.

  intros eps Heps.

  specialize (Hcvg eps Heps).
  destruct Hcvg as [N HN].

  exists N.
  intros n Hn.

  specialize (HN (S (S n))).

  assert (Hshift : (N <= S (S n))%nat) by lia.
  specialize (HN Hshift).

  rewrite scalar_exp_partial_remainder_decomp in HN.

  unfold R_dist in HN |- *.

  replace
    (scalar_exp_remainder x n - (exp x - 1 - x))
    with
    ((1 + x + scalar_exp_remainder x n) - exp x)
    by ring.

  exact HN.
Qed.

Lemma fact_shift2 :
  forall k,
    fact (S (S k))
    =
    (S (S k) * S k * fact k)%nat.
Proof.
  intro k.
  simpl.
  ring.
Qed.

Lemma fact_shift2_ge :
  forall k,
    (2 * fact k <= fact (S (S k)))%nat.
Proof.
  intro k.
  rewrite fact_shift2.

  assert (Hf : (0 < fact k)%nat).
  {
    apply fact_pos.
  }

  nia.
Qed.

Lemma inv_fact_shift2_le :
  forall k,
    inv_fact (S (S k))
    <= / 2 * inv_fact k.
Proof.
  intro k.
  unfold inv_fact.

  assert (Hfk : 0 < INR (fact k)).
  {
    apply lt_0_INR.
    apply fact_pos.
  }

  assert (Hle :
    2 * INR (fact k)
    <= INR (fact (S (S k)))).
  {
    pose proof (fact_shift2_ge k) as Hnat.
    apply le_INR in Hnat.

    replace (2 * INR (fact k))
      with (INR (2 * fact k)%nat).
    - exact Hnat.
    - rewrite mult_INR.
      simpl.
      ring.
  }

  rewrite <- Rinv_mult.

  apply Rinv_le_contravar.
  - apply Rmult_lt_0_compat.
    + lra.
    + exact Hfk.
  - exact Hle.
Qed.

Lemma scalar_remainder_term_le :
  forall x k,
    0 <= x ->
    inv_fact (S (S k)) * x^(S (S k))
    <=
    (x^2 / 2) * (inv_fact k * x^k).
Proof.
  intros x k Hx.

  assert (Hpow : 0 <= x ^ (S (S k))).
  {
    apply pow_le.
    exact Hx.
  }

  eapply Rle_trans.

  - apply Rmult_le_compat_r.
    + exact Hpow.
    + apply inv_fact_shift2_le.

  - replace (x ^ (S (S k)))
      with (x^2 * x^k).
    2: {
      simpl.
      ring.
    }

    assert (Heq :
      / 2 * inv_fact k * (x ^ 2 * x ^ k)
      =
      x ^ 2 / 2 * (inv_fact k * x ^ k)).
    {
      unfold Rdiv.
      ring.
    }

    rewrite Heq.
    apply Rle_refl.
Qed.

Lemma scalar_exp_remainder_le_partial :
  forall x N,
    0 <= x ->
    scalar_exp_remainder x N
    <=
    (x^2 / 2) * scalar_exp_partial x N.
Proof.
  intros x N Hx.
  induction N as [| N IH].

  - cbn [scalar_exp_remainder scalar_exp_partial].

    pose proof
      (scalar_remainder_term_le x 0 Hx)
      as Hterm.

    exact Hterm.

  - cbn [scalar_exp_remainder scalar_exp_partial].

    eapply Rle_trans.

    + apply Rplus_le_compat.

      * exact IH.

      * apply scalar_remainder_term_le.
        exact Hx.

    + assert (Heq :
        x ^ 2 / 2 * scalar_exp_partial x N
        + x ^ 2 / 2 * (inv_fact (S N) * x ^ S N)
        =
        x ^ 2 / 2 *
          (scalar_exp_partial x N
           + inv_fact (S N) * x ^ S N)).
      {
        ring.
      }

      rewrite Heq.
      apply Rle_refl.
Qed.

Lemma exp_second_order_remainder_bound :
  forall x : R,
    0 <= x ->
    exp x - 1 - x
    <=
    (x * x / 2) * exp x.
Proof.
  intros x Hx.

  (* Prove the result by contradiction. *)
  apply Rnot_lt_le.
  intro Hbad.

  (* ---------------------------------------------------------- *)
  (* Basic positivity facts.                                   *)
  (* ---------------------------------------------------------- *)

  assert (Hc :
    0 <= x * x / 2).
  {
    nra.
  }

  assert (Hgap :
    0 <
      (exp x - 1 - x)
      - (x * x / 2) * exp x).
  {
    lra.
  }

  assert (Hone :
    0 < 1 + x * x / 2).
  {
    nra.
  }

  assert (Hden :
    0 < 2 * (1 + x * x / 2)).
  {
    nra.
  }

  (* ---------------------------------------------------------- *)
  (* Choose epsilon from the positive gap.                      *)
  (*                                                            *)
  (*   eps = gap / (2(1 + x^2/2)).                             *)
  (* ---------------------------------------------------------- *)

  set
    (eps :=
       ((exp x - 1 - x)
        - (x * x / 2) * exp x)
       /
       (2 * (1 + x * x / 2))).

  assert (Heps : 0 < eps).
  {
    unfold eps.
    apply Rdiv_lt_0_compat.
    - exact Hgap.
    - exact Hden.
  }

  (* ---------------------------------------------------------- *)
  (* Use convergence of the scalar remainder and partial sum.   *)
  (* ---------------------------------------------------------- *)

  pose proof
    (scalar_exp_remainder_cvg x)
    as Hrem.

  pose proof
    (scalar_exp_partial_cvg x)
    as Hpartial.

  unfold Un_cv in Hrem.
  unfold Un_cv in Hpartial.

  specialize (Hrem eps Heps).
  specialize (Hpartial eps Heps).

  destruct Hrem as [Nr Hrem].
  destruct Hpartial as [Np Hpartial].

  pose (N := Nat.max Nr Np).

  assert (HrN : (Nr <= N)%nat).
  {
    unfold N.
    apply Nat.le_max_l.
  }

  assert (HpN : (Np <= N)%nat).
  {
    unfold N.
    apply Nat.le_max_r.
  }

  specialize (Hrem N HrN).
  specialize (Hpartial N HpN).

  (* ---------------------------------------------------------- *)
  (* Finite Taylor remainder estimate.                          *)
  (* ---------------------------------------------------------- *)

  pose proof
    (scalar_exp_remainder_le_partial x N Hx)
    as Hfinite.

  (* Normalize x^2 to x*x so all expressions have the same
     syntactic form. *)
  assert (Hsq :
    x ^ 2 = x * x).
  {
    ring.
  }

  rewrite Hsq in Hfinite.

  (* ---------------------------------------------------------- *)
  (* Extract the useful one-sided convergence estimates.        *)
  (* ---------------------------------------------------------- *)

  unfold R_dist in Hrem.
  unfold R_dist in Hpartial.

  assert (Hrem_low :
    (exp x - 1 - x) - eps
    <
    scalar_exp_remainder x N).
  {
    apply Rabs_def2 in Hrem.
    destruct Hrem as [_ Hlow].
    lra.
  }

  assert (Hpartial_up :
    scalar_exp_partial x N
    <
    exp x + eps).
  {
    apply Rabs_def2 in Hpartial.
    destruct Hpartial as [Hup _].
    lra.
  }

  (* Since x^2/2 >= 0, multiply the partial-sum estimate
     without reversing the inequality. *)
  assert (Hscaled :
    (x * x / 2) * scalar_exp_partial x N
    <=
    (x * x / 2) * (exp x + eps)).
  {
    apply Rmult_le_compat_l.
    - exact Hc.
    - apply Rlt_le.
      exact Hpartial_up.
  }

  (* ---------------------------------------------------------- *)
  (* Combine the three estimates.                              *)
  (*                                                            *)
  (* exp(x)-1-x-eps                                            *)
  (*       < remainder_N                                       *)
  (*       <= (x^2/2) partial_N                                *)
  (*       <= (x^2/2)(exp(x)+eps).                             *)
  (* ---------------------------------------------------------- *)

  assert (Hchain :
    (exp x - 1 - x) - eps
    <
    (x * x / 2) * (exp x + eps)).
  {
    eapply Rlt_le_trans.
    - exact Hrem_low.
    - eapply Rle_trans.
      + exact Hfinite.
      + exact Hscaled.
  }

  (* Rearrange Hchain:

       gap < (1 + x^2/2) * eps.
  *)
  assert (Hgap_small :
    (exp x - 1 - x)
      - (x * x / 2) * exp x
    <
    (1 + x * x / 2) * eps).
  {
    nra.
  }


  assert (Hden_ne :
    2 * (1 + x * x / 2) <> 0).
  {
    lra.
  }

  assert (Heps_mul :
    eps * (2 * (1 + x * x / 2))
    =
    (exp x - 1 - x)
      - (x * x / 2) * exp x).
  {
    unfold eps.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
- ring.
- exact Hden_ne.
  }

  (* From eps * [2(1+c)] = gap, obtain
       (1+c)eps = gap/2.
     No division manipulation is necessary: nra can handle the
     remaining polynomial equality. *)
  assert (Heps_half :
    (1 + x * x / 2) * eps
    =
    (((exp x - 1 - x)
       - (x * x / 2) * exp x) / 2)).
  {
    nra.
  }

  (* Hgap_small now says gap < gap/2. *)
  rewrite Heps_half in Hgap_small.

  (* But Hgap says gap > 0, contradiction. *)
  nra.
Qed.
