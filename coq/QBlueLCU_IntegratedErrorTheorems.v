(***********************************************************************
 QBlueLCU_IntegratedErrorTheorems.v

***********************************************************************)
From Coq Require Import Reals.Reals.
From Coq Require Import Reals.RIneq.
From Coq Require Import Lia Lra Field.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQuantumWalk.
Require Import QBlue.QBlueQSPCore.
Require Import QBlue.QBlueQSVT_updateQSP.
Require Import QBlue.QBlueQSVT.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Local Open Scope R_scope.

Section Budget.
  Lemma segment_budget :
    forall (r : nat) (eps delta : R),
      (1 <= r)%nat -> 0 <= delta ->
      delta <= eps / INR r -> INR r * delta <= eps.
  Proof.
    intros r eps delta Hr Hdelta Hbound.
    assert (Hpos : 0 < INR r) by (apply lt_0_INR; lia).
    assert (H : INR r * delta <= INR r * (eps / INR r)).
    { apply Rmult_le_compat_l; lra. }
    replace (INR r * (eps / INR r)) with eps in H.
    - exact H.
    - unfold Rdiv.
      field; lra.
  Qed.

Lemma component_budget :
  forall (eps : R) (r : nat)
         (poly phase implementation : R),
    (1 <= r)%nat ->
    0 <= poly ->
    0 <= phase ->
    0 <= implementation ->
    poly + phase + implementation <= eps / INR r ->
    INR r * (poly + phase + implementation) <= eps.
Proof.
  intros eps r poly phase implementation
         Hr Hpoly Hphase Himpl Hbudget.
  apply segment_budget.
  - exact Hr.
  - lra.
  - exact Hbudget.
Qed.

End Budget.

Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S k => iterate f k (f x)
  end.

Section CertifiedIteration.
  Context {State : Type}.
  Variable dist : State -> State -> R.
  Hypothesis dist_refl : forall x, dist x x = 0.
  Hypothesis dist_triangle :
    forall a b c, dist a c <= dist a b + dist b c.
  Variable actual ideal : State -> State.
  Hypothesis actual_nonexpansive :
    forall a b, dist (actual a) (actual b) <= dist a b.
  Variable good : State -> Prop.
  Hypothesis good_preserved : forall x, good x -> good (ideal x).
  Variable delta : R.
  Hypothesis delta_nonneg : 0 <= delta.
  Hypothesis local_accuracy :
    forall x, good x -> dist (actual x) (ideal x) <= delta.

  Lemma iter_nonexpansive :
    forall n a b, dist (iterate actual n a) (iterate actual n b) <= dist a b.
  Proof.
    induction n as [|n IH]; intros a b; simpl.
    - apply Rle_refl.
    - eapply Rle_trans; [apply IH | apply actual_nonexpansive].
  Qed.

Theorem iter_error :
  forall n x, good x ->
    dist (iterate actual n x)
         (iterate ideal n x) <= INR n * delta.
Proof.
  induction n as [|n IH]; intros x Hx; simpl.
  - rewrite dist_refl; lra.
  - pose proof
      (iter_nonexpansive n (actual x) (ideal x))
      as Hnonexp.

    pose proof (local_accuracy x Hx) as Hlocal.

    pose proof
      (IH (ideal x) (good_preserved x Hx))
      as Htail.

    pose proof
      (dist_triangle
        (iterate actual n (actual x))
        (iterate actual n (ideal x))
        (iterate ideal n (ideal x)))
      as Htri.

    change (
      dist (iterate actual n (actual x))
           (iterate ideal n (ideal x))
      <= INR (S n) * delta).

    rewrite S_INR.
    lra.
Qed.



  Theorem iter_error_budget :
    forall n eps x,
      (1 <= n)%nat -> good x ->
      delta <= eps / INR n ->
      dist (iterate actual n x) (iterate ideal n x) <= eps.
  Proof.
    intros n eps x Hn Hx Hb.
    eapply Rle_trans; [apply iter_error; exact Hx|].
    apply segment_budget; assumption.
  Qed.
End CertifiedIteration.


Definition qwalk_r (lp : lowprog) (t : R) : nat :=
  qwalk_segments (lcu_terms lp) t.
Definition qwalk_tau (lp : lowprog) (t : R) : R :=
  lcu_lambda (lcu_terms lp) * t / INR (qwalk_r lp t).
Definition qwalk_K (lp : lowprog) (t eps : R) : nat :=
  Nat.max 1 (findK_qwalk (qwalk_tau lp t) (eps / (4 * INR (qwalk_r lp t)))).
Definition qwalk_step (eps t : R) (nbit : nat) (lp : lowprog) : gl :=
  let terms := lcu_terms lp in
  let k := qwalk_K lp t eps in
  let m := Nat.max 1 (Nat.log2_up (S k)) in
  let l := qwalk_alloc nbit (idx_width terms) m in
  oaa (qwalk_segment nbit terms (qwalk_tau lp t) k l)
      (ql_idx l ++ ql_outer l ++ [ql_pad l]) (ql_work l).

Lemma qwalk_circuit_unfold :
  forall eps t nbit lp,
    qwalk_circuit eps t nbit lp =
    repeat_gl (qwalk_r lp t) (qwalk_step eps t nbit lp).
Proof. reflexivity. Qed.

Definition qsvt_r (lp : lowprog) (t : R) : nat :=
  qsvt_segments (lcu_terms lp) t.
Definition qsvt_tau (lp : lowprog) (t : R) : R :=
  lcu_lambda (lcu_terms lp) * t / INR (qsvt_r lp t).
Definition qsvt_step (eps t : R) (nbit : nat) (lp : lowprog) : gl :=
  let terms := lcu_terms lp in
  let e := eps / (8 * INR (qsvt_r lp t)) in
  let l := qsvt_alloc nbit (idx_width terms) in
  oaa (qsvt_segment nbit terms (qsvt_tau lp t) e e l)
      (vl_idx l ++ [vl_f l; vl_r l; vl_s l]) (vl_work l).

Lemma qsvt_circuit_unfold :
  forall eps t nbit lp,
    qsvt_circuit eps t nbit lp =
    repeat_gl (qsvt_r lp t) (qsvt_step eps t nbit lp).
Proof. reflexivity. Qed.

(* Generic circuit semantics bridge: sequential gates and repeat. *)
Section CircuitSemantics.
  Context {State : Type}.
  Variable run : gl -> State -> State.
  Hypothesis run_empty : forall x, run [] x = x.
  Hypothesis run_append :
    forall a b x, run (a ++ b) x = run b (run a x).

  Lemma run_repeat : forall n a x,
    run (repeat_gl n a) x = iterate (run a) n x.
  Proof.
    induction n as [|n IH]; intros a x; simpl.
    - apply run_empty.
    - rewrite run_append, IH; reflexivity.
  Qed.
End CircuitSemantics.

Section QBlueTheorems.
  Context {State : Type}.
  Variable distance : State -> State -> R.
  Hypothesis distance_refl : forall x, distance x x = 0.
  Hypothesis distance_triangle :
    forall a b c, distance a c <= distance a b + distance b c.
  Variable run : gl -> State -> State.
  Hypothesis run_empty : forall x, run [] x = x.
  Hypothesis run_append :
    forall a b x, run (a ++ b) x = run b (run a x).

  Variable clean : State -> Prop.
  Variable ideal_step : R -> State -> State.
  Hypothesis ideal_step_preserves_clean :
    forall dt x, clean x -> clean (ideal_step dt x).

  (* This is the evolution semigroup law specialized to the r segments.
     Prove it later from the matrix exponential of the source Hamiltonian. *)
  Variable ideal_total : R -> State -> State.
  Hypothesis ideal_segment_composition :
    forall t r x, (1 <= r)%nat ->
      iterate (ideal_step (t / INR r)) r x = ideal_total t x.

  Theorem QuantumWalk_Compilation_Correctness :
    forall eps t nbit lp delta x,
      clean x ->
      0 <= delta ->
      delta <= eps / INR (qwalk_r lp t) ->
      (forall a b,
          distance (run (qwalk_step eps t nbit lp) a)
                   (run (qwalk_step eps t nbit lp) b)
          <= distance a b) ->
      (forall a, clean a ->
          distance (run (qwalk_step eps t nbit lp) a)
                   (ideal_step (t / INR (qwalk_r lp t)) a)
          <= delta) ->
      distance (run (qwalk_circuit eps t nbit lp) x)
               (ideal_total t x) <= eps.
  Proof.
    intros eps t nbit lp delta x Hclean Hd Hbudget Hnonexp Hlocal.
    rewrite qwalk_circuit_unfold.
    rewrite (run_repeat run run_empty run_append).
    rewrite <- (ideal_segment_composition t (qwalk_r lp t) x).
    2: { unfold qwalk_r, qwalk_segments; lia. }
    eapply (iter_error_budget distance distance_refl distance_triangle
                (run (qwalk_step eps t nbit lp))
                (ideal_step (t / INR (qwalk_r lp t)))
                Hnonexp clean
                (ideal_step_preserves_clean (t / INR (qwalk_r lp t)))
                delta Hd Hlocal).
    - unfold qwalk_r, qwalk_segments; lia.
    - exact Hclean.
    - exact Hbudget.
  Qed.

  Theorem QSVT_Compilation_Correctness :
    forall eps t nbit lp delta x,
      clean x ->
      0 <= delta ->
      delta <= eps / INR (qsvt_r lp t) ->
      (forall a b,
          distance (run (qsvt_step eps t nbit lp) a)
                   (run (qsvt_step eps t nbit lp) b)
          <= distance a b) ->
      (forall a, clean a ->
          distance (run (qsvt_step eps t nbit lp) a)
                   (ideal_step (t / INR (qsvt_r lp t)) a)
          <= delta) ->
      distance (run (qsvt_circuit eps t nbit lp) x)
               (ideal_total t x) <= eps.
  Proof.
    intros eps t nbit lp delta x Hclean Hd Hbudget Hnonexp Hlocal.
    rewrite qsvt_circuit_unfold.
    rewrite (run_repeat run run_empty run_append).
    rewrite <- (ideal_segment_composition t (qsvt_r lp t) x).
    2: { unfold qsvt_r, qsvt_segments; lia. }
    eapply (iter_error_budget distance distance_refl distance_triangle
                (run (qsvt_step eps t nbit lp))
                (ideal_step (t / INR (qsvt_r lp t)))
                Hnonexp clean
                (ideal_step_preserves_clean (t / INR (qsvt_r lp t)))
                delta Hd Hlocal).
    - unfold qsvt_r, qsvt_segments; lia.
    - exact Hclean.
    - exact Hbudget.
  Qed.
End QBlueTheorems.

Inductive lcu_method : Type :=
| TaylorMethod | QuantumWalkMethod | QSPMethod | QSVTMethod.

Record lcu_local_errors := {
  approximation_error : R;
  phase_error : R;
  lcu_error : R;
  amplification_error : R;
  implementation_error : R
}.

Definition local_error_sum (e : lcu_local_errors) : R :=
  approximation_error e + phase_error e + lcu_error e +
  amplification_error e + implementation_error e.

Theorem four_method_budget :
  forall (method : lcu_method) (r : nat) (eps : R)
         (e : lcu_local_errors),
    (1 <= r)%nat ->
    0 <= local_error_sum e ->
    local_error_sum e <= eps / INR r ->
    INR r * local_error_sum e <= eps.
Proof.
  intros method r eps e Hr Hnonneg Hb.
  eapply segment_budget; eassumption.
Qed.

