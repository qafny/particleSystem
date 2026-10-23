

(***************************************************************
 * QBlueTrotterProof_1.v
 *
 * Finite structural correctness of first-order and
 * second-order Trotterization.

 ***************************************************************)

From Coq Require Import Reals List Arith Lia Psatz.

Require Import QuantumLib.Matrix.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueHamiltonian.
Require Import QBlue.QBlueMatNorm.
Require Import QBlue.QBlueMatrixExp.
Require Import QBlue.QBlueTrotter_1.

Import ListNotations.
Local Open Scope R_scope.

(* ============================================================ *)
(* 1. Repetition of Hamiltonian programs                        *)
(* ============================================================ *)

Fixpoint repeat_prog
  (k : nat) (p : norm_prog) : norm_prog :=
  match k with
  | O => []
  | S j => p ++ repeat_prog j p
  end.

Lemma repeat_prog_length :
  forall k p,
    length (repeat_prog k p) =
    (k * length p)%nat.
Proof.
  induction k as [| k IH]; intros p; simpl.
  - reflexivity.
  - rewrite app_length, IH.
    lia.
Qed.

(* ============================================================ *)
(* 2. Reverse-append accumulator correctness                    *)
(* ============================================================ *)

Lemma rev_append_acc :
  forall (A : Type) (p acc : list A),
    rev (rev_append p acc) = rev acc ++ p.
Proof.
  intros A p.
  induction p as [| x xs IH]; intro acc.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IH.
    simpl.
rewrite <- app_assoc.
reflexivity.
Qed.

Lemma trotter_nstep_acc_correct :
  forall k p acc,
    trotter_nstep_acc k p acc =
    rev acc ++ repeat_prog k p.
Proof.
  induction k as [| k IH]; intros p acc.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl trotter_nstep_acc.
    rewrite IH.
    rewrite rev_append_acc.
    simpl repeat_prog.
    rewrite app_assoc.
    reflexivity.
Qed.

(* ============================================================ *)
(* 3. Trotter repetition correctness                            *)
(* ============================================================ *)

Lemma trotter_nstep_correct :
  forall k p,
    trotter_nstep k p = repeat_prog k p.
Proof.
  intros k p.
  unfold trotter_nstep.
  rewrite trotter_nstep_acc_correct.
  simpl.
  reflexivity.
Qed.

Lemma trotter_nstep_length_proof :
  forall k p,
    length (trotter_nstep k p) =
    (k * length p)%nat.
Proof.
  intros k p.
  rewrite trotter_nstep_correct.
  apply repeat_prog_length.
Qed.

(* ============================================================ *)
(* 4. Positive step counts                                      *)
(* ============================================================ *)

Lemma trotter_step_nonzero :
  forall err t d p,
    (0 < trotter_step err t d p)%nat.
Proof.
  intros err t d p.
  unfold trotter_step.
  destruct (Rlt_dec 0 err); lia.
Qed.

Lemma trotter_step_2nd_order_nonzero :
  forall err t d p,
    (0 < trotter_step_2nd_order err t d p)%nat.
Proof.
  intros err t d p.
  unfold trotter_step_2nd_order.
  destruct (Rlt_dec 0 err); lia.
Qed.

(* ============================================================ *)
(* 5. First-order program length                               *)
(* ============================================================ *)

Lemma trotter_length_proof :
  forall err t d p,
    length (trotter err t d p) =
    (trotter_step err t d p * length p)%nat.
Proof.
  intros err t d p.
  unfold trotter.
  rewrite trotter_nstep_length_proof.
  unfold trotter_astep, mult_r_normprog.
  rewrite map_length.
  reflexivity.
Qed.

(* ============================================================ *)
(* 6. Second-order program length                              *)
(* ============================================================ *)

Lemma trotter_2nd_order_length_proof :
  forall err t d p,
    length (trotter_2nd_order err t d p) =
    (trotter_step_2nd_order err t d p *
      (2 * length p))%nat.
Proof.
  intros err t d p.
  unfold trotter_2nd_order.
  rewrite trotter_nstep_length_proof.
  unfold trotter_astep, mult_r_normprog.
  rewrite app_length.
  repeat rewrite map_length.
  rewrite rev_length.
  f_equal.
  simpl.
rewrite Nat.add_0_r.
reflexivity.
Qed.


(* ============================================================ *)
(* 7. Hermiticity of generated Hamiltonians                    *)
(* ============================================================ *)

Lemma trotter_hamiltonian_hermitian :
  forall err t d p,
    is_hermitian_mat
      (norm_prog2mat (trotter err t d p) d).
Proof.
  intros.
  apply hermitian_norm_prog2mat.
Qed.

Lemma trotter_2nd_hamiltonian_hermitian :
  forall err t d p,
    is_hermitian_mat
      (norm_prog2mat (trotter_2nd_order err t d p) d).
Proof.
  intros.
  apply hermitian_norm_prog2mat.
Qed.

(* A generic N-fold telescope: if every replacement costs at most
   delta, the total cost is bounded by N * delta. This is purely
   arithmetic; the matrix-norm telescope must be proved elsewhere. *)
Lemma error_sum_le_uniform :
  forall (N : nat) (delta : R) (cost : nat -> R),
    (forall k, (k < N)%nat -> cost k <= delta) ->
    forall k, (k <= N)%nat ->
      (fix sum_cost (j : nat) : R :=
         match j with
         | O => 0
         | S j' => sum_cost j' + cost j'
         end) k
      <= INR k * delta.
Proof.
  intros N delta cost Hcost k Hk.
  induction k as [| k IH].
  - simpl.
    rewrite Rmult_0_l.
    right.
    reflexivity.

  - simpl.

    assert (Hsum :
      (fix sum_cost (j : nat) : R :=
         match j with
         | O => 0
         | S j' => sum_cost j' + cost j'
         end) k <= INR k * delta).
    {
      apply IH.
      lia.
    }

    assert (Hck : cost k <= delta).
    {
      apply Hcost.
      lia.
    }

    replace
      (match k with
       | O => 1
       | S _ => INR k + 1
       end)
      with (INR k + 1).
    + nra.
    + destruct k as [| k']; simpl; ring.
Qed.


Theorem first_order_budget_bridge :
  forall (N : nat) (t C1 err actual_error : R),
    (0 < N)%nat ->
    0 <= C1 ->
    0 <= actual_error ->
    actual_error <= INR N * ((t / INR N)^2 * C1 / 2) ->
    t^2 * C1 / (2 * INR N) <= err ->
    actual_error <= err.
Proof.
  intros N t C1 err actual_error HN HC Hnonneg Hlocal Hbudget.
  assert (Hpos : 0 < INR N) by (apply lt_0_INR; lia).
  eapply Rle_trans; [exact Hlocal|].
  eapply Rle_trans; [|exact Hbudget].
  unfold Rdiv.
  field_simplify; try lra.
Qed.

(* Same argument for a second-order local error proportional to
   |t/N|^3.  The actual matrix estimate must be supplied by a
   separate, fully proved operator-norm theorem. *)
Theorem second_order_budget_bridge :
  forall (N : nat) (t C2 err actual_error : R),
    (0 < N)%nat ->
    0 <= C2 ->
    0 <= actual_error ->
    actual_error <= INR N * ((Rabs t / INR N)^3 * C2) ->
    (Rabs t)^3 * C2 / (INR N)^2 <= err ->
    actual_error <= err.
Proof.
  intros N t C2 err actual_error HN HC Hnonneg Hlocal Hbudget.
  assert (Hpos : 0 < INR N) by (apply lt_0_INR; lia).
  eapply Rle_trans; [exact Hlocal|].
  eapply Rle_trans; [|exact Hbudget].
  unfold Rdiv.
  field_simplify; try lra.
Qed.

(* The fully explicit version is independent of symbolic positivity. *)
Theorem trotter_first_order_accuracy_if_budget :
  forall err t d p actual_error,
    0 <= actual_error ->
    actual_error <=
      INR (trotter_step err t d p) *
      ((t / INR (trotter_step err t d p))^2 *
       comm_sum1 (pauli_terms d p) / 2) ->
    t^2 * comm_sum1 (pauli_terms d p) /
      (2 * INR (trotter_step err t d p)) <= err ->
    actual_error <= err.
Proof.
  intros err t d p actual_error Hnonneg Hlocal Hbudget.
  assert (Hpos : 0 < INR (trotter_step err t d p)).
  { apply lt_0_INR. unfold trotter_step.
    destruct (Rlt_dec 0 err); lia. }
  eapply Rle_trans; [exact Hlocal|].
  eapply Rle_trans; [|exact Hbudget].
  unfold Rdiv.
  field_simplify; try lra.
Qed.

Theorem trotter_second_order_accuracy_if_budget :
  forall err t d p actual_error,
    0 <= actual_error ->
    actual_error <=
      INR (trotter_step_2nd_order err t d p) *
      ((Rabs t / INR (trotter_step_2nd_order err t d p))^3 *
       comm_sum2 (pauli_terms d (rev p))) ->
    (Rabs t)^3 * comm_sum2 (pauli_terms d (rev p)) /
      INR (trotter_step_2nd_order err t d p)^2 <= err ->
    actual_error <= err.
Proof.
  intros err t d p actual_error Hnonneg Hlocal Hbudget.
  assert (Hpos : 0 < INR (trotter_step_2nd_order err t d p)).
  { apply lt_0_INR. unfold trotter_step_2nd_order.
    destruct (Rlt_dec 0 err); lia. }
  eapply Rle_trans; [exact Hlocal|].
  eapply Rle_trans; [|exact Hbudget].
  unfold Rdiv.
  field_simplify; try lra.
Qed.


(* Although t affects the selected step count, it does not enter
   the per-step Hamiltonian coefficient. Thus the generated program
   generally represents unit-time evolution, not time-t evolution. *)

(* A nontrivial, testable structural statement: all generated
   Hamiltonian matrices are well formed and Hermitian. *)
Lemma first_order_generated_WF :
  forall err t d p,
    WF_Matrix (norm_prog2mat (trotter err t d p) d).
Proof.
  intros; apply wf_norm_prog2mat.
Qed.

Lemma second_order_generated_WF :
  forall err t d p,
    WF_Matrix (norm_prog2mat (trotter_2nd_order err t d p) d).
Proof.
  intros; apply wf_norm_prog2mat.
Qed.

Lemma first_order_generated_hermitian :
  forall err t d p,
    is_hermitian_mat (norm_prog2mat (trotter err t d p) d).
Proof.
  intros; apply hermitian_norm_prog2mat.
Qed.

Lemma second_order_generated_hermitian :
  forall err t d p,
    is_hermitian_mat (norm_prog2mat (trotter_2nd_order err t d p) d).
Proof.
  intros; apply hermitian_norm_prog2mat.
Qed.

(* These are genuine conditional arithmetic accuracy results.
   The local/global norm bound and the step-budget inequality
   are supplied explicitly; neither is smuggled in as an axiom. *)
Theorem first_order_accuracy_from_obligations :
  forall err t d p (actual_error : R),
    actual_error <=
      INR (trotter_step err t d p) *
      ((t / INR (trotter_step err t d p))^2 *
       comm_sum1 (pauli_terms d p) / 2) ->
    t^2 * comm_sum1 (pauli_terms d p) /
      (2 * INR (trotter_step err t d p)) <= err ->
    actual_error <= err.
Proof.
  intros err t d p actual_error Hlocal Hbudget.
  set (N := trotter_step err t d p) in *.
  assert (HN : 0 < INR N).
  { apply lt_0_INR. unfold N. apply trotter_step_positive. }
  assert (Heq :
    INR N * ((t / INR N)^2 * comm_sum1 (pauli_terms d p) / 2) =
    t^2 * comm_sum1 (pauli_terms d p) / (2 * INR N)).
  { field. lra. }
  rewrite Heq in Hlocal.
  eapply Rle_trans; eassumption.
Qed.

Theorem second_order_accuracy_from_obligations :
  forall err t d p (actual_error : R),
    actual_error <=
      INR (trotter_step_2nd_order err t d p) *
      ((Rabs t / INR (trotter_step_2nd_order err t d p))^3 *
       comm_sum2 (pauli_terms d (rev p))) ->
    (Rabs t)^3 * comm_sum2 (pauli_terms d (rev p)) /
      INR (trotter_step_2nd_order err t d p)^2 <= err ->
    actual_error <= err.
Proof.
  intros err t d p actual_error Hlocal Hbudget.
  set (N := trotter_step_2nd_order err t d p) in *.
  assert (HN : 0 < INR N).
  { apply lt_0_INR. unfold N. apply trotter_step_2nd_order_positive. }
  assert (Heq :
    INR N * ((Rabs t / INR N)^3 *
      comm_sum2 (pauli_terms d (rev p))) =
    (Rabs t)^3 * comm_sum2 (pauli_terms d (rev p)) / INR N^2).
  { field. lra. }
  rewrite Heq in Hlocal.
  eapply Rle_trans; eassumption.
Qed.


(* Algebraic telescope, written as a one-step recurrence.
   WF conditions are essential for the matrix algebra lemmas. *)
Lemma matrix_power_difference_step :
  forall n (A B : Square n) k,
    WF_Matrix A -> WF_Matrix B ->
    Mminus (matrix_power A (S k)) (matrix_power B (S k)) =
    Mplus
      (Mmult (Mminus A B) (matrix_power A k))
      (Mmult B (Mminus (matrix_power A k) (matrix_power B k))).
Proof.
  intros n A B k HA HB.
  simpl.
  unfold Mminus.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  (* Convert B * (-A^k) and (-B) * A^k to a common form. *)
  rewrite Mopp_mult_r.
  rewrite Mopp_mult_l.
  lma.
Qed.

Lemma real_pow_le_one :
  forall (x : R) (k : nat),
    0 <= x ->
    x <= 1 ->
    x ^ k <= 1.
Proof.
  intros x k Hx Hx1.
  induction k as [| k IHk].
  - simpl. lra.
  - simpl.
    assert (Hpow_nonneg : 0 <= x ^ k).
    { apply pow_le. exact Hx. }
    nra.
Qed.
(* Norm recurrence: with ||A||, ||B|| <= 1, each step costs
   at most ||A-B||. *)
Lemma matrix_power_error_bound :
  forall n (A B : Square n) k,
    WF_Matrix A -> WF_Matrix B ->
    mnorm n A <= 1 -> mnorm n B <= 1 ->
    mnorm n (Mminus (matrix_power A k) (matrix_power B k))
      <= INR k * mnorm n (Mminus A B).
Proof.
  intros n A B k HA HB HAn HBn.
  induction k as [| k IH].
  - simpl.
    unfold Mminus.
    unfold Mopp.
replace (I n .+ - C1 .* I n)
  with (@Zero n n).
2:{
  unfold scale, Mplus, Zero.
  prep_matrix_equality.
  lca.
}
rewrite mnorm_zero.
rewrite Rmult_0_l.
apply Rle_refl.
  - rewrite matrix_power_difference_step by assumption.
    eapply Rle_trans.
    { apply mnorm_triangle. }
    eapply Rle_trans.
    { apply Rplus_le_compat; apply mnorm_submult. }
assert (Hpow : mnorm n (matrix_power A k) <= 1).
{
  eapply Rle_trans.
  - apply mnorm_matrix_power_le.
  - apply real_pow_le_one.
    + apply mnorm_nonneg.
    + exact HAn.
}

    pose proof (mnorm_nonneg n (Mminus A B)) as Hdiff.
    pose proof (mnorm_nonneg n (Mminus (matrix_power A k) (matrix_power B k))) as Hprev.
    rewrite S_INR.
    nra.
Qed.






















