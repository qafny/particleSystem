
(* QBlueMarQSim_FullCorrected.v *)
From Coq Require Import List Reals Arith Lia.
Import ListNotations.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueMarQSim.

Local Open Scope R_scope.
Local Open Scope list_scope.


Definition marqsim_lambda (lp : lowprog) : R :=
  sum_w lp (length lp).

Definition marqsim_initial_distribution (lp : lowprog) : list R :=
  let lam := marqsim_lambda lp in
  map (fun theta => Rabs theta / lam) (get_coef lp).

Fixpoint marqsim_sample_acc
  (pi : list R)
  (lp : lowprog)
  (previous : option nat)
  (Nsample : nat)
  (P : nat -> list R)
  (acc : lowprog)
  : lowprog :=
  match Nsample with
  | O => rev acc
  | S n' =>
      let rn := random_float 1 in
      let current_distribution :=
        match previous with
        | None => pi
        | Some i => P i
        end in
      let next_index :=
        sample_aterm_markov current_distribution rn 0 in
      let '(coef, H_i) :=
        nth_default (C0, fun _ => paulii) lp next_index in
      let sampled_term :=
        if Rltb (fst coef) R0
        then (RtoC (Rminus R0 R1), H_i)
        else (C1, H_i) in
      marqsim_sample_acc
        pi lp (Some next_index) n' P (sampled_term :: acc)
  end.

Definition marqsim_sample
  (lp : lowprog)
  (Nsample : nat)
  (P : nat -> list R)
  : lowprog :=
  marqsim_sample_acc
    (marqsim_initial_distribution lp)
    lp None Nsample P [].

Definition trotter_marqsim_paper
  (err t : R)
  (lp : lowprog)
  (P : nat -> list R)
  : lowprog :=
  let N := qdrift_step err t lp in
  let lam := marqsim_lambda lp in
  mult_r_hplus
    (lam * t / INR N)
    (marqsim_sample lp N P).

Definition marqsim_mixed_transition
  (lp : lowprog)
  (mix : R)
  (graph_transition : nat -> list R)
  : nat -> list R :=
  get_trans_MarQdrift lp mix graph_transition.

Definition trotter_marqsim_mixed
  (err t : R)
  (lp : lowprog)
  (mix : R)
  (graph_transition : nat -> list R)
  : lowprog :=
  trotter_marqsim_paper
    err t lp
    (marqsim_mixed_transition lp mix graph_transition).

Lemma length_marqsim_sample_acc :
  forall pi lp previous N P acc,
    length (marqsim_sample_acc pi lp previous N P acc)
    =
    (N + length acc)%nat.
Proof.
  intros pi lp previous N.
  revert previous.

  induction N as [|N IH].

  - intros previous P acc.
    simpl.
    rewrite rev_length.
    lia.

  - intros previous P acc.
    destruct previous as [i|].

    + simpl.

      remember (random_float 1) as rn eqn:Hr.
      remember (sample_aterm_markov (P i) rn 0)
        as next_index eqn:Hnext.

      destruct
        (nth_default (C0, fun _ => paulii) lp next_index)
        as [coef H_i] eqn:Hnth.

      destruct (Rltb (fst coef) R0) eqn:Hsgn;
        simpl;
        rewrite (IH (Some next_index) P);
        simpl;
        lia.

    + simpl.

      remember (random_float 1) as rn eqn:Hr.
      remember (sample_aterm_markov pi rn 0)
        as next_index eqn:Hnext.

      destruct
        (nth_default (C0, fun _ => paulii) lp next_index)
        as [coef H_i] eqn:Hnth.

      destruct (Rltb (fst coef) R0) eqn:Hsgn;
        simpl;
        rewrite (IH (Some next_index) P);
        simpl;
        lia.
Qed.

Theorem length_marqsim_sample :
  forall lp N P,
    length (marqsim_sample lp N P) = N.
Proof.
  intros lp N P.
  unfold marqsim_sample.
  rewrite length_marqsim_sample_acc.
  simpl.
  lia.
Qed.

Definition marqsim_current_distribution
  (pi : list R)
  (P : nat -> list R)
  (previous : option nat)
  : list R :=
  match previous with
  | None => pi
  | Some i => P i
  end.

Lemma marqsim_current_distribution_first :
  forall pi P,
    marqsim_current_distribution pi P None = pi.
Proof.
  reflexivity.
Qed.

Lemma marqsim_current_distribution_next :
  forall pi P i,
    marqsim_current_distribution pi P (Some i) = P i.
Proof.
  reflexivity.
Qed.

Definition MarQKernel := nat -> nat -> R.

Fixpoint marqsim_sum_first
  (n : nat)
  (f : nat -> R)
  : R :=
  match n with
  | O => 0
  | S n' => marqsim_sum_first n' f + f n'
  end.

Definition marqsim_prob_vector
  (n : nat)
  (pi : nat -> R)
  : Prop :=
  (forall i, (i < n)%nat -> 0 <= pi i)
  /\
  marqsim_sum_first n pi = 1.

Definition marqsim_stochastic_kernel
  (n : nat)
  (P : MarQKernel)
  : Prop :=
  forall i,
    (i < n)%nat ->
    (forall j, (j < n)%nat -> 0 <= P i j)
    /\
    marqsim_sum_first n (P i) = 1.

Definition marqsim_stationary_kernel
  (n : nat)
  (pi : nat -> R)
  (P : MarQKernel)
  : Prop :=
  forall j,
    (j < n)%nat ->
    marqsim_sum_first n
      (fun i => pi i * P i j)
    =
    pi j.

Inductive marqsim_reachable
  (n : nat)
  (P : MarQKernel)
  : nat -> nat -> Prop :=
| marqsim_reachable_refl :
    forall i,
      (i < n)%nat ->
      marqsim_reachable n P i i
| marqsim_reachable_step :
    forall i j k,
      marqsim_reachable n P i j ->
      (j < n)%nat ->
      (k < n)%nat ->
      0 < P j k ->
      marqsim_reachable n P i k.

Definition marqsim_strongly_connected
  (n : nat)
  (P : MarQKernel)
  : Prop :=
  forall i j,
    (i < n)%nat ->
    (j < n)%nat ->
    marqsim_reachable n P i j.

Record MarQSimPaperConditions
  (n : nat)
  (pi : nat -> R)
  (P : MarQKernel)
  : Prop := {
  marqsim_cond_prob :
    marqsim_prob_vector n pi;
  marqsim_cond_stochastic :
    marqsim_stochastic_kernel n P;
  marqsim_cond_stationary :
    marqsim_stationary_kernel n pi P;
  marqsim_cond_connected :
    marqsim_strongly_connected n P
}.


(******************************************************************************)
(* Finite-sum algebra                                                         *)
(******************************************************************************)

Lemma marqsim_sum_first_ext :
  forall n (f g : nat -> R),
    (forall i, (i < n)%nat -> f i = g i) ->
    marqsim_sum_first n f = marqsim_sum_first n g.
Proof.
  intros n.
  induction n as [|n IH]; intros f g Hfg.
  - reflexivity.
  - simpl.
    rewrite (IH f g).
    + rewrite Hfg by lia.
      reflexivity.
    + intros i Hi.
      apply Hfg.
      lia.
Qed.

Lemma marqsim_sum_first_plus :
  forall n (f g : nat -> R),
    marqsim_sum_first n (fun i => f i + g i)
    =
    marqsim_sum_first n f + marqsim_sum_first n g.
Proof.
  intros n f g.
  induction n as [|n IH].
  - simpl; ring.
  - simpl.
    rewrite IH.
    ring.
Qed.

Lemma marqsim_sum_first_scale_l :
  forall n (a : R) (f : nat -> R),
    marqsim_sum_first n (fun i => a * f i)
    =
    a * marqsim_sum_first n f.
Proof.
  intros n a f.
  induction n as [|n IH].
  - simpl; ring.
  - simpl.
    rewrite IH.
    ring.
Qed.

Lemma marqsim_sum_first_scale_r :
  forall n (a : R) (f : nat -> R),
    marqsim_sum_first n (fun i => f i * a)
    =
    marqsim_sum_first n f * a.
Proof.
  intros n a f.
  induction n as [|n IH].
  - simpl; ring.
  - simpl.
    rewrite IH.
    ring.
Qed.


(******************************************************************************)
(* qDRIFT/reset kernel and mixed MarQSim kernel                               *)
(******************************************************************************)

(* Every row is pi. *)
Definition marqsim_reset_kernel
  (pi : nat -> R)
  : MarQKernel :=
  fun _ j => pi j.

(* P_mix = alpha * P + (1-alpha) * Q. *)
Definition marqsim_mix_kernel
  (alpha : R)
  (P Q : MarQKernel)
  : MarQKernel :=
  fun i j =>
    alpha * P i j
    +
    (1 - alpha) * Q i j.


(******************************************************************************)
(* Reset kernel is stochastic and stationary                                  *)
(******************************************************************************)

Lemma marqsim_reset_stochastic :
  forall n pi,
    marqsim_prob_vector n pi ->
    marqsim_stochastic_kernel n
      (marqsim_reset_kernel pi).
Proof.
  intros n pi Hpi.
  destruct Hpi as [Hnonneg Hsum].
  intros i Hi.
  split.
  - intros j Hj.
    unfold marqsim_reset_kernel.
    apply Hnonneg.
    exact Hj.
  - unfold marqsim_reset_kernel.
    exact Hsum.
Qed.

Lemma marqsim_reset_stationary :
  forall n pi,
    marqsim_prob_vector n pi ->
    marqsim_stationary_kernel n pi
      (marqsim_reset_kernel pi).
Proof.
  intros n pi Hpi.
  destruct Hpi as [Hnonneg Hsum].
  intros j Hj.
  unfold marqsim_reset_kernel.
  rewrite marqsim_sum_first_scale_r.
  rewrite Hsum.
  ring.
Qed.


(******************************************************************************)
(* Convex mixtures preserve stochasticity                                     *)
(******************************************************************************)

Lemma marqsim_mix_stochastic :
  forall n alpha P Q,
    0 <= alpha <= 1 ->
    marqsim_stochastic_kernel n P ->
    marqsim_stochastic_kernel n Q ->
    marqsim_stochastic_kernel n
      (marqsim_mix_kernel alpha P Q).
Proof.
  intros n alpha P Q Halpha HP HQ.
  intros i Hi.

  specialize (HP i Hi).
  specialize (HQ i Hi).

  destruct HP as [HPnonneg HPsum].
  destruct HQ as [HQnonneg HQsum].

  split.
  - intros j Hj.
    unfold marqsim_mix_kernel.

    assert (HPj : 0 <= P i j).
    { apply HPnonneg. exact Hj. }

    assert (HQj : 0 <= Q i j).
    { apply HQnonneg. exact Hj. }

    assert (Ha : 0 <= alpha) by lra.
    assert (H1a : 0 <= 1 - alpha) by lra.
assert (Hleft : 0 <= alpha * P i j).
{
  nra.
}

assert (Hright : 0 <= (1 - alpha) * Q i j).
{
  nra.
}

    lra.

  - unfold marqsim_mix_kernel.
    rewrite marqsim_sum_first_plus.
    rewrite !marqsim_sum_first_scale_l.
    rewrite HPsum, HQsum.
    ring.
Qed.


(******************************************************************************)
(* Convex mixtures preserve a common stationary distribution                   *)
(******************************************************************************)

Lemma marqsim_mix_stationary :
  forall n pi alpha P Q,
    marqsim_stationary_kernel n pi P ->
    marqsim_stationary_kernel n pi Q ->
    marqsim_stationary_kernel n pi
      (marqsim_mix_kernel alpha P Q).
Proof.
  intros n pi alpha P Q HP HQ.
  intros j Hj.
  unfold marqsim_mix_kernel.

  assert (Hdist :
    marqsim_sum_first n
      (fun i =>
         pi i *
         (alpha * P i j + (1 - alpha) * Q i j))
    =
    alpha *
      marqsim_sum_first n
        (fun i => pi i * P i j)
    +
    (1 - alpha) *
      marqsim_sum_first n
        (fun i => pi i * Q i j)).
  {
    rewrite <-
      (marqsim_sum_first_scale_l
         n alpha
         (fun i => pi i * P i j)).

    rewrite <-
      (marqsim_sum_first_scale_l
         n (1 - alpha)
         (fun i => pi i * Q i j)).

    rewrite <- marqsim_sum_first_plus.

    apply marqsim_sum_first_ext.
    intros i Hi.
    ring.
  }

  rewrite Hdist.
  rewrite (HP j Hj).
  rewrite (HQ j Hj).
  ring.
Qed.


(******************************************************************************)
(* First major structural theorem                                              *)
(******************************************************************************)

Theorem marqsim_mixture_preserves_target :
  forall n pi alpha graphP,
    marqsim_prob_vector n pi ->
    0 <= alpha <= 1 ->
    marqsim_stochastic_kernel n graphP ->
    marqsim_stationary_kernel n pi graphP ->
    marqsim_stochastic_kernel n
      (marqsim_mix_kernel
         alpha
         graphP
         (marqsim_reset_kernel pi))
    /\
    marqsim_stationary_kernel n pi
      (marqsim_mix_kernel
         alpha
         graphP
         (marqsim_reset_kernel pi)).
Proof.
  intros n pi alpha graphP
    Hpi Halpha Hstoch Hstationary.

  split.
  - eapply marqsim_mix_stochastic.
    + exact Halpha.
    + exact Hstoch.
    + apply marqsim_reset_stochastic.
      exact Hpi.

  - eapply marqsim_mix_stationary.
    + exact Hstationary.
    + apply marqsim_reset_stationary.
      exact Hpi.
Qed.


(******************************************************************************)
(* One-step stationarity                                                      *)
(******************************************************************************)

Theorem marqsim_one_step_preserves_pi :
  forall n pi P j,
    marqsim_stationary_kernel n pi P ->
    (j < n)%nat ->
    marqsim_sum_first n
      (fun i => pi i * P i j)
    =
    pi j.
Proof.
  intros n pi P j Hstat Hj.
  apply Hstat.
  exact Hj.
Qed.



(******************************************************************************)
(* If the reset component has positive weight and pi has full support, then    *)
(* every mixed transition has strictly positive probability.                   *)
(******************************************************************************)
Lemma marqsim_mix_positive :
  forall n pi alpha graphP i j,
    0 <= alpha < 1 ->
    (forall k, (k < n)%nat -> 0 < pi k) ->
    marqsim_stochastic_kernel n graphP ->
    (i < n)%nat ->
    (j < n)%nat ->
    0 <
    marqsim_mix_kernel
      alpha
      graphP
      (marqsim_reset_kernel pi)
      i j.
Proof.
  intros n pi alpha graphP i j
    Halpha Hpi_pos Hgraph Hi Hj.

  unfold marqsim_mix_kernel.
  unfold marqsim_reset_kernel.

  specialize (Hgraph i Hi).
  destruct Hgraph as [Hgraph_nonneg Hgraph_sum].

  assert (HPij : 0 <= graphP i j).
  {
    apply Hgraph_nonneg.
    exact Hj.
  }

  assert (Hpij : 0 < pi j).
  {
    apply Hpi_pos.
    exact Hj.
  }

  nra.
Qed.




(******************************************************************************)
(* Strict positivity gives strong connectivity immediately: every state has a  *)
(* positive-probability one-step edge to every other state.                    *)
(******************************************************************************)

Theorem marqsim_mix_strongly_connected :
  forall n pi alpha graphP,
    0 <= alpha < 1 ->
    (forall k, (k < n)%nat -> 0 < pi k) ->
    marqsim_stochastic_kernel n graphP ->
    marqsim_strongly_connected n
      (marqsim_mix_kernel
         alpha
         graphP
         (marqsim_reset_kernel pi)).
Proof.
  intros n pi alpha graphP
    Halpha Hpi_pos Hgraph.

  unfold marqsim_strongly_connected.
  intros i j Hi Hj.

  eapply marqsim_reachable_step
    with (j := i).

  - apply marqsim_reachable_refl.
    exact Hi.

  - exact Hi.

  - exact Hj.

  - eapply marqsim_mix_positive.
    + exact Halpha.
    + exact Hpi_pos.
    + exact Hgraph.
    + exact Hi.
    + exact Hj.
Qed.


Theorem marqsim_mixture_satisfies_paper_conditions :
  forall n pi alpha graphP,
    marqsim_prob_vector n pi ->
    (forall k, (k < n)%nat -> 0 < pi k) ->
    0 <= alpha < 1 ->
    marqsim_stochastic_kernel n graphP ->
    marqsim_stationary_kernel n pi graphP ->
    MarQSimPaperConditions
      n
      pi
      (marqsim_mix_kernel
         alpha
         graphP
         (marqsim_reset_kernel pi)).
Proof.
  intros n pi alpha graphP
    Hpi Hpi_pos Halpha Hgraph_stoch Hgraph_stat.

  constructor.

  - exact Hpi.

  - eapply marqsim_mix_stochastic.
    + lra.
    + exact Hgraph_stoch.
    + apply marqsim_reset_stochastic.
      exact Hpi.

  - eapply marqsim_mix_stationary.
    + exact Hgraph_stat.
    + apply marqsim_reset_stationary.
      exact Hpi.

  - eapply marqsim_mix_strongly_connected.
    + exact Halpha.
    + exact Hpi_pos.
    + exact Hgraph_stoch.
Qed.



(******************************************************************************)
(*                                                                            *)
(* Main result:                                                               *)
(*                                                                            *)
(*   the executable list-based MarQSim transition                             *)
(*                                                                            *)
(*       get_trans_MarQdrift lp alpha graph_transition                        *)
(*                                                                            *)
(*   denotes exactly                                                          *)
(*                                                                            *)
(*       alpha P_graph + (1-alpha) P_qDRIFT                                   *)
(*                                                                            *)
(* provided every graph row has the same length as the qDRIFT distribution.   *)
(*                                                                            *)
(* Consequently, all structural MarQSim properties proved                   *)
(*  transfer to the executable implementation.                               *)

(******************************************************************************)






(******************************************************************************)
(*  Total lookup of a real-valued list                                      *)
(*                                                                            *)
(* nthR xs i = xs[i] when i is in range, and 0 otherwise.                     *)
(*                                                                            *)
(* Using a total lookup makes it possible to view a list-valued transition    *)
(* matrix as the mathematical kernel nat -> nat -> R.                         *)
(******************************************************************************)

Definition marqsim_nthR
  (xs : list R)
  (i : nat)
  : R :=
  nth i xs 0.


Lemma marqsim_nthR_nil :
  forall i,
    marqsim_nthR [] i = 0.
Proof.
  intros i.
  unfold marqsim_nthR.
  destruct i; reflexivity.
Qed.


Lemma marqsim_nthR_cons_0 :
  forall x xs,
    marqsim_nthR (x :: xs) 0 = x.
Proof.
  reflexivity.
Qed.


Lemma marqsim_nthR_cons_S :
  forall x xs i,
    marqsim_nthR (x :: xs) (S i)
    =
    marqsim_nthR xs i.
Proof.
  reflexivity.
Qed.


(******************************************************************************)
(*  Convert executable lists into mathematical functions                    *)
(******************************************************************************)

Definition marqsim_list_probability
  (pi : list R)
  : nat -> R :=
  fun j =>
    marqsim_nthR pi j.


Definition marqsim_list_kernel
  (P : nat -> list R)
  : MarQKernel :=
  fun i j =>
    marqsim_nthR (P i) j.


(******************************************************************************)
(*  qDRIFT probability distribution used by the executable implementation   *)
(*                                                                            *)
(* The executable initial distribution is                                     *)
(*                                                                            *)
(*                    |theta_i|                                               *)
(*             pi_i = ---------.                                              *)
(*                      lambda                                                *)
(*                                                                            *)
(******************************************************************************)

Definition marqsim_pi_list
  (lp : lowprog)
  : list R :=
  marqsim_initial_distribution lp.


Definition marqsim_pi
  (lp : lowprog)
  : nat -> R :=
  marqsim_list_probability
    (marqsim_pi_list lp).


Definition marqsim_num_states
  (lp : lowprog)
  : nat :=
  length (marqsim_pi_list lp).


(******************************************************************************)
(*  Mathematical graph kernel                                               *)
(******************************************************************************)

Definition marqsim_graph_kernel
  (graph_transition : nat -> list R)
  : MarQKernel :=
  marqsim_list_kernel graph_transition.


(******************************************************************************)
(*  Mathematical executable MarQSim kernel                                  *)
(*                                                                            *)
(* This is simply the list-based implementation viewed pointwise as           *)
(* nat -> nat -> R.                                                           *)
(******************************************************************************)

Definition marqsim_executable_kernel
  (lp : lowprog)
  (alpha : R)
  (graph_transition : nat -> list R)
  :MarQKernel :=
  marqsim_list_kernel
    (get_trans_MarQdrift
       lp
       alpha
       graph_transition).


(******************************************************************************)
(*  Abstract verified MarQSim kernel                                        *)
(*                                                                            *)
(*     P_mix = alpha P_graph + (1-alpha) P_reset                              *)
(*                                                                            *)
(* where every row of P_reset is pi.                                          *)
(******************************************************************************)

Definition marqsim_abstract_kernel
  (lp : lowprog)
  (alpha : R)
  (graph_transition : nat -> list R)
  :MarQKernel :=
  marqsim_mix_kernel
    alpha
    (marqsim_graph_kernel graph_transition)
    (marqsim_reset_kernel
       (marqsim_pi lp)).


(******************************************************************************)
(*  Row-shape well-formedness                                               *)

(******************************************************************************)

Definition marqsim_rows_well_formed
  (lp : lowprog)
  (graph_transition : nat -> list R)
  : Prop :=
  forall i,
    length (graph_transition i)
    =
    length (marqsim_pi_list lp).


(******************************************************************************)
(* Fundamental list mixture lemma                                          *)
(*                                                                            *)
(* mix_rows alpha xs ys computes pointwise                                    *)
(*                                                                            *)
(*        alpha * xs[j] + (1-alpha) * ys[j].                                  *)
(******************************************************************************)
Lemma marqsim_nthR_mix_rows :
  forall alpha xs ys,
    length xs = length ys ->
    forall j,
      marqsim_nthR
        (mix_rows alpha xs ys)
        j
      =
      alpha * marqsim_nthR xs j
      +
      (1 - alpha) * marqsim_nthR ys j.
Proof.
  intros alpha xs.
  induction xs as [|x xs IH];
    intros ys Hlen j.

  - destruct ys as [|y ys].
    + destruct j;
        unfold marqsim_nthR, mix_rows;
        simpl;
        ring.
    + simpl in Hlen.
      discriminate.

  - destruct ys as [|y ys].
    + simpl in Hlen.
      discriminate.

    + simpl in Hlen.
      injection Hlen as Htail.

      destruct j as [|j].

      * unfold marqsim_nthR, mix_rows.
        simpl.
        ring.

      * unfold marqsim_nthR, mix_rows.
        simpl.
        apply IH.
        exact Htail.
Qed.



(******************************************************************************)
(*  Executable qDRIFT probability list equals the corrected front-end pi   *)
(******************************************************************************)

Lemma marqsim_pi_list_unfold :
  forall lp,
    marqsim_pi_list lp
    =
    map
      (fun theta =>
         Rabs theta /
         marqsim_lambda lp)
      (get_coef lp).
Proof.
  intros lp.
  unfold marqsim_pi_list.
  unfold marqsim_initial_distribution.
  reflexivity.
Qed.


Lemma marqsim_lambda_unfold :
  forall lp,
    marqsim_lambda lp
    =
    sum_w lp (length lp).
Proof.
  intros lp.
  unfold marqsim_lambda.
  reflexivity.
Qed.


(******************************************************************************)
(*  The probability list used by get_trans_MarQdrift is exactly pi         *)
(******************************************************************************)

Lemma marqsim_get_trans_probability_list :
  forall lp,
    map
      (fun x =>
         Rabs x /
         sum_w lp (length lp))
      (get_coef lp)
    =
    marqsim_pi_list lp.
Proof.
  intros lp.

  unfold marqsim_pi_list.
  unfold marqsim_initial_distribution.
  unfold marqsim_lambda.

  reflexivity.
Qed.


Theorem get_trans_MarQdrift_matches_mix_kernel_pointwise :
  forall lp alpha graph_transition i j,
    marqsim_rows_well_formed
      lp
      graph_transition ->
    marqsim_executable_kernel
      lp
      alpha
      graph_transition
      i j
    =
    marqsim_abstract_kernel
      lp
      alpha
      graph_transition
      i j.
Proof.
  intros lp alpha graph_transition i j Hrows.

  unfold marqsim_executable_kernel.
  unfold marqsim_list_kernel.

  unfold marqsim_abstract_kernel.
  unfold marqsim_mix_kernel.
  unfold marqsim_reset_kernel.
  unfold marqsim_graph_kernel.
  unfold marqsim_pi.
  unfold marqsim_list_probability.

  unfold get_trans_MarQdrift.

  cbn.

  rewrite marqsim_nthR_mix_rows.

  - reflexivity.

  - specialize (Hrows i).

    unfold marqsim_pi_list in Hrows.
    unfold marqsim_initial_distribution in Hrows.
    unfold marqsim_lambda in Hrows.

    exact Hrows.
Qed.


(******************************************************************************)
(*  Kernel extensional equality                                            *)

(******************************************************************************)

Theorem get_trans_MarQdrift_matches_mix_kernel :
  forall lp alpha graph_transition,
    marqsim_rows_well_formed
      lp
      graph_transition ->
    marqsim_executable_kernel
      lp
      alpha
      graph_transition
    =
    marqsim_abstract_kernel
      lp
      alpha
      graph_transition.
Proof.
  intros lp alpha graph_transition Hrows.

  apply functional_extensionality.
  intro i.

  apply functional_extensionality.
  intro j.

  apply
    get_trans_MarQdrift_matches_mix_kernel_pointwise.

  exact Hrows.
Qed.


(******************************************************************************)
(*  Explicit refinement relation                                           *)

(******************************************************************************)

Definition marqsim_transition_refines
  (n : nat)
  (T : nat -> list R)
  (P : MarQKernel)
  : Prop :=
  forall i j,
    (i < n)%nat ->
    (j < n)%nat ->
    marqsim_nthR (T i) j
    =
    P i j.


(******************************************************************************)
(*  Graph transition trivially refines its list-kernel interpretation       *)
(******************************************************************************)

Lemma marqsim_graph_transition_refines :
  forall n graph_transition,
    marqsim_transition_refines
      n
      graph_transition
      (marqsim_graph_kernel graph_transition).
Proof.
  intros n graph_transition.
  unfold marqsim_transition_refines.
  unfold marqsim_graph_kernel.
  unfold marqsim_list_kernel.

  intros i j Hi Hj.
  reflexivity.
Qed.


(******************************************************************************)
(*  Executable MarQSim transition refines the verified abstract kernel      *)
(******************************************************************************)

Theorem executable_marqsim_transition_refines :
  forall lp alpha graph_transition,
    marqsim_rows_well_formed
      lp
      graph_transition ->
    marqsim_transition_refines
      (marqsim_num_states lp)
      (get_trans_MarQdrift
         lp
         alpha
         graph_transition)
      (marqsim_abstract_kernel
         lp
         alpha
         graph_transition).
Proof.
  intros lp alpha graph_transition Hrows.

  unfold marqsim_transition_refines.

  intros i j Hi Hj.

  change
    (marqsim_executable_kernel
       lp alpha graph_transition i j
     =
     marqsim_abstract_kernel
       lp alpha graph_transition i j).

  apply
    get_trans_MarQdrift_matches_mix_kernel_pointwise.

  exact Hrows.
Qed.


(******************************************************************************)
(*  Structural correctness of the abstract mixed kernel                    *)

(******************************************************************************)

Theorem marqsim_abstract_kernel_satisfies_paper_conditions :
  forall lp alpha graph_transition,
    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    MarQSimPaperConditions
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_abstract_kernel
         lp
         alpha
         graph_transition).
Proof.
  intros
    lp
    alpha
    graph_transition
    Hpi
    Hpi_pos
    Halpha
    Hgraph_stoch
    Hgraph_stationary.

  unfold marqsim_abstract_kernel.

  apply
    marqsim_mixture_satisfies_paper_conditions.

  - exact Hpi.

  - exact Hpi_pos.

  - exact Halpha.

  - exact Hgraph_stoch.

  - exact Hgraph_stationary.
Qed.


(******************************************************************************)
(* MAIN EXECUTABLE STRUCTURAL CORRECTNESS THEOREM                          *)

(******************************************************************************)

Theorem QBlue_MarQSim_Executable_Correct :
  forall lp alpha graph_transition,

    marqsim_rows_well_formed
      lp
      graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    MarQSimPaperConditions
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp
         alpha
         graph_transition).
Proof.
  intros
    lp
    alpha
    graph_transition
    Hrows
    Hpi
    Hpi_pos
    Halpha
    Hgraph_stoch
    Hgraph_stationary.

  rewrite
    (get_trans_MarQdrift_matches_mix_kernel
       lp
       alpha
       graph_transition
       Hrows).

  apply
    marqsim_abstract_kernel_satisfies_paper_conditions.

  - exact Hpi.

  - exact Hpi_pos.

  - exact Halpha.

  - exact Hgraph_stoch.

  - exact Hgraph_stationary.
Qed.


(******************************************************************************)
(*  Individual executable consequences                                     *)

(******************************************************************************)

Corollary QBlue_MarQSim_Executable_Stochastic :
  forall lp alpha graph_transition,

    marqsim_rows_well_formed
      lp
      graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_executable_kernel
         lp alpha graph_transition).
Proof.
  intros
    lp alpha graph_transition
    Hrows Hpi Hpi_pos Halpha
    Hgraph_stoch Hgraph_stationary.

  pose proof
    (QBlue_MarQSim_Executable_Correct
       lp alpha graph_transition
       Hrows
       Hpi
       Hpi_pos
       Halpha
       Hgraph_stoch
       Hgraph_stationary)
    as HC.

destruct HC as
  [HC_prob
   HC_stoch
   HC_stationary
   HC_connected].

exact HC_stoch.
Qed.


Corollary QBlue_MarQSim_Executable_Stationary :
  forall lp alpha graph_transition,

    marqsim_rows_well_formed
      lp
      graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp alpha graph_transition).
Proof.
  intros
    lp alpha graph_transition
    Hrows Hpi Hpi_pos Halpha
    Hgraph_stoch Hgraph_stationary.

  pose proof
    (QBlue_MarQSim_Executable_Correct
       lp alpha graph_transition
       Hrows
       Hpi
       Hpi_pos
       Halpha
       Hgraph_stoch
       Hgraph_stationary)
    as HC.

destruct HC as
  [HC_prob
   HC_stoch
   HC_stationary
   HC_connected].

exact HC_stationary.
Qed.

Corollary QBlue_MarQSim_Executable_StronglyConnected :
  forall lp alpha graph_transition,

    marqsim_rows_well_formed
      lp
      graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_strongly_connected
      (marqsim_num_states lp)
      (marqsim_executable_kernel
         lp alpha graph_transition).
Proof.
  intros
    lp alpha graph_transition
    Hrows Hpi Hpi_pos Halpha
    Hgraph_stoch Hgraph_stationary.

  pose proof
    (QBlue_MarQSim_Executable_Correct
       lp alpha graph_transition
       Hrows
       Hpi
       Hpi_pos
       Halpha
       Hgraph_stoch
       Hgraph_stationary)
    as HC.

  destruct HC as
    [HC_prob
     HC_stoch
     HC_stationary
     HC_connected].

  exact HC_connected.
Qed.


(******************************************************************************)
(*  The executable transition preserves the qDRIFT target distribution      *)

(******************************************************************************)

Corollary QBlue_MarQSim_Executable_Preserves_Pi :
  forall lp alpha graph_transition,

    marqsim_rows_well_formed
      lp
      graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition) ->

    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition) ->

    forall j,
      (j < marqsim_num_states lp)%nat ->

      marqsim_sum_first
        (marqsim_num_states lp)
        (fun i =>
           marqsim_pi lp i
           *
           marqsim_executable_kernel
             lp alpha graph_transition i j)
      =
      marqsim_pi lp j.
Proof.
  intros
    lp alpha graph_transition
    Hrows Hpi Hpi_pos Halpha
    Hgraph_stoch Hgraph_stationary.

  pose proof
    (QBlue_MarQSim_Executable_Stationary
       lp alpha graph_transition
       Hrows
       Hpi
       Hpi_pos
       Halpha
       Hgraph_stoch
       Hgraph_stationary)
    as Hstationary.

  unfold marqsim_stationary_kernel
    in Hstationary.

  exact Hstationary.
Qed.


Theorem QBlue_MarQSim_Sample_Count :
  forall pi lp previous N P acc,
    length
      (marqsim_sample_acc
         pi lp previous N P acc)
    =
    (N + length acc)%nat.
Proof.
  intros pi lp previous N P acc.
  apply length_marqsim_sample_acc.
Qed.

Theorem QBlue_MarQSim_Sample_Length :
  forall lp N P,
    length (marqsim_sample lp N P) = N.
Proof.
  intros lp N P.
  unfold marqsim_sample.
  rewrite length_marqsim_sample_acc.
  simpl.
  lia.
Qed.

(******************************************************************************)
(*                                                          *)
(*                                                                            *)
(* FullCorrected uses                                                         *)
(*                                                                            *)
(*                       lambda * t                                           *)
(*                       ----------                                           *)
(*                            N                                               *)
(*                                                                            *)
(* for every sampled Pauli term, matching the qDRIFT / MarQSim simulation     *)
(* step.                                                                      *)
(******************************************************************************)

Definition marqsim_paper_step_scale
  (lp : lowprog)
  (t : R)
  (N : nat)
  : R :=
  marqsim_lambda lp
  *
  t
  /
  INR N.


Lemma marqsim_paper_step_scale_unfold :
  forall lp t N,
    marqsim_paper_step_scale lp t N
    =
    sum_w lp (length lp)
    *
    t
    /
    INR N.
Proof.
  intros lp t N.
  unfold marqsim_paper_step_scale.
  unfold marqsim_lambda.
  reflexivity.
Qed.


(******************************************************************************)
(*  correctness record                                                  *)
(******************************************************************************)

Record QBlueMarQSimCorrect
  (lp : lowprog)
  (alpha : R)
  (graph_transition : nat -> list R)
  : Prop :=
{
  qblue_marqsim_rows :
    marqsim_rows_well_formed
      lp
      graph_transition;

  qblue_marqsim_probability :
    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp);

  qblue_marqsim_positive_support :
    forall k,
      (k < marqsim_num_states lp)%nat ->
      0 < marqsim_pi lp k;

  qblue_marqsim_mix_range :
    0 <= alpha < 1;

  qblue_marqsim_graph_stochastic :
    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition);

  qblue_marqsim_graph_stationary :
    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition)
}.


(******************************************************************************)
(*  FINAL STRUCTURAL CORRECTNESS THEOREM                                    *)
(******************************************************************************)

Theorem QBlue_MarQSim_Main_Correctness :
  forall lp alpha graph_transition,

    QBlueMarQSimCorrect
      lp
      alpha
      graph_transition ->

    MarQSimPaperConditions
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp
         alpha
         graph_transition).
Proof.
  intros lp alpha graph_transition HC.

  destruct HC as
    [Hrows
     Hpi
     Hpos
     Halpha
     Hgraph_stoch
     Hgraph_stationary].

  apply
    QBlue_MarQSim_Executable_Correct.

  - exact Hrows.
  - exact Hpi.
  - exact Hpos.
  - exact Halpha.
  - exact Hgraph_stoch.
  - exact Hgraph_stationary.
Qed.


(******************************************************************************)
(*  Final refinement theorem                                               *)
(******************************************************************************)

Theorem QBlue_MarQSim_Implementation_Refines_Verified_Kernel :
  forall lp alpha graph_transition,

    QBlueMarQSimCorrect
      lp
      alpha
      graph_transition ->

    marqsim_executable_kernel
      lp
      alpha
      graph_transition
    =
    marqsim_mix_kernel
      alpha
      (marqsim_graph_kernel graph_transition)
      (marqsim_reset_kernel
         (marqsim_pi lp)).
Proof.
  intros lp alpha graph_transition HC.

  destruct HC as
    [Hrows
     Hpi
     Hpos
     Halpha
     Hgraph_stoch
     Hgraph_stationary].

  apply
    get_trans_MarQdrift_matches_mix_kernel.

  exact Hrows.
Qed.


(******************************************************************************)
(* N-step MarQSim distribution semantics                                       *)
(******************************************************************************)

Definition marqsim_distribution_step
  (n : nat)
  (mu : nat -> R)
  (P : MarQKernel)
  : nat -> R :=
  fun j =>
    marqsim_sum_first n
      (fun i => mu i * P i j).

Fixpoint marqsim_distribution_after
  (n : nat)
  (steps : nat)
  (mu : nat -> R)
  (P : MarQKernel)
  : nat -> R :=
  match steps with
  | O => mu
  | S k =>
      marqsim_distribution_step
        n
        (marqsim_distribution_after n k mu P)
        P
  end.


Lemma marqsim_stationary_is_fixed_point :
  forall n pi P,
    marqsim_stationary_kernel n pi P ->
    forall j,
      (j < n)%nat ->
      marqsim_distribution_step n pi P j = pi j.
Proof.
  intros n pi P Hstat j Hj.
  unfold marqsim_distribution_step.
  unfold marqsim_stationary_kernel in Hstat.
  apply Hstat.
  exact Hj.
Qed.

Theorem marqsim_stationary_after_N_steps :
  forall n pi P N j,
    marqsim_stationary_kernel n pi P ->
    (j < n)%nat ->
    marqsim_distribution_after n N pi P j = pi j.
Proof.

  intros n pi P N.
  induction N as [|N IH].
  - intros j Hstat Hj.
    simpl.
    reflexivity.

  - intros j Hstat Hj.
    simpl.

    rewrite <- (Hstat j Hj).

    apply marqsim_sum_first_ext.
    intros i Hi.

    rewrite (IH i Hstat Hi).
    reflexivity.
Qed.

Theorem QBlue_MarQSim_Executable_Preserves_Pi_N_Steps :
  forall lp alpha graph_transition N j,

    QBlueMarQSimCorrect
      lp
      alpha
      graph_transition ->

    (j < marqsim_num_states lp)%nat ->

    marqsim_distribution_after
      (marqsim_num_states lp)
      N
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp alpha graph_transition)
      j
    =
    marqsim_pi lp j.
Proof.
  intros lp alpha graph_transition N j HC Hj.

  destruct HC as
    [Hrows
     Hpi
     Hpos
     Halpha
     Hgraph_stoch
     Hgraph_stationary].

  apply marqsim_stationary_after_N_steps.

  - apply QBlue_MarQSim_Executable_Stationary
      with
        (graph_transition := graph_transition).

    + exact Hrows.
    + exact Hpi.
    + exact Hpos.
    + exact Halpha.
    + exact Hgraph_stoch.
    + exact Hgraph_stationary.

  - exact Hj.
Qed.

Theorem QBlue_MarQSim_Algorithm_Verified :
  forall lp alpha graph_transition N,

    QBlueMarQSimCorrect
      lp alpha graph_transition ->

    (* implementation is exactly the verified mixed kernel *)
    marqsim_executable_kernel
      lp alpha graph_transition
    =
    marqsim_mix_kernel
      alpha
      (marqsim_graph_kernel graph_transition)
      (marqsim_reset_kernel (marqsim_pi lp))

    /\

    (* exactly N Hamiltonian terms are sampled *)
    (forall P,
       length (marqsim_sample lp N P) = N)

    /\

    (* after every finite number of Markov steps,
       the marginal remains the qDRIFT distribution *)
    (forall k j,
       (j < marqsim_num_states lp)%nat ->
       marqsim_distribution_after
         (marqsim_num_states lp)
         k
         (marqsim_pi lp)
         (marqsim_executable_kernel
            lp alpha graph_transition)
         j
       =
       marqsim_pi lp j).
Proof.
  intros lp alpha graph_transition N HC.

  split.

  - apply QBlue_MarQSim_Implementation_Refines_Verified_Kernel.
    exact HC.

  - split.

    + intros P.
      apply QBlue_MarQSim_Sample_Length.

    + intros k j Hj.
      eapply QBlue_MarQSim_Executable_Preserves_Pi_N_Steps.
      * exact HC.
      * exact Hj.
Qed.




(******************************************************************************)

(*                                                                            *)
(*       P(i,j) = f(H_i^prev,H_j^next) / pi_i                                *)
(*                                                                            *)
(* The source-flow equality gives                                              *)
(*                                                                            *)
(*       sum_j f(i,j) = pi_i                                                   *)
(*                                                                            *)
(* and the sink-flow equality / flow conservation gives                        *)
(*                                                                            *)
(*       sum_i f(i,j) = pi_j.                                                  *)
(*                                                                            *)
(* Hence                                                                       *)
(*                                                                            *)
(*       (pi P)_j                                                             *)
(*         = sum_i pi_i * (f(i,j)/pi_i)                                       *)
(*         = sum_i f(i,j)                                                      *)
(*         = pi_j.                                                             *)
(******************************************************************************)

Definition marqsim_flow : Type :=
  nat -> nat -> R.

Definition marqsim_flow_transition
  (pi : nat -> R)
  (f : marqsim_flow)
  : MarQKernel :=
  fun i j =>
    f i j / pi i.

Definition marqsim_flow_nonnegative
  (n : nat)
  (f : marqsim_flow)
  : Prop :=
  forall i j,
    (i < n)%nat ->
    (j < n)%nat ->
    0 <= f i j.

(* Flow leaving H_i^prev equals the source flow pi_i. *)
Definition marqsim_flow_source_constraint
  (n : nat)
  (pi : nat -> R)
  (f : marqsim_flow)
  : Prop :=
  forall i,
    (i < n)%nat ->
    marqsim_sum_first n (f i) = pi i.

(* Flow entering H_j^next equals the sink flow pi_j. *)
Definition marqsim_flow_sink_constraint
  (n : nat)
  (pi : nat -> R)
  (f : marqsim_flow)
  : Prop :=
  forall j,
    (j < n)%nat ->
    marqsim_sum_first n (fun i => f i j) = pi j.

Lemma marqsim_flow_transition_nonnegative :
  forall n pi f,
    (forall i, (i < n)%nat -> 0 < pi i) ->
    marqsim_flow_nonnegative n f ->
    forall i j,
      (i < n)%nat ->
      (j < n)%nat ->
      0 <= marqsim_flow_transition pi f i j.
Proof.
  intros n pi f Hpi Hf i j Hi Hj.
  unfold marqsim_flow_transition, Rdiv.

  assert (Hfi : 0 <= f i j).
  {
    apply Hf; assumption.
  }

  assert (Hinv : 0 < / pi i).
  {
    apply Rinv_0_lt_compat.
    apply Hpi.
    exact Hi.
  }

  nra.
Qed.

Lemma marqsim_flow_transition_row_sum :
  forall n pi f,
    (forall i, (i < n)%nat -> 0 < pi i) ->
    marqsim_flow_source_constraint n pi f ->
    forall i,
      (i < n)%nat ->
      marqsim_sum_first n
        (marqsim_flow_transition pi f i)
      = 1.
Proof.
  intros n pi f Hpi Hsource i Hi.

  unfold marqsim_flow_transition.
  unfold Rdiv.

  rewrite marqsim_sum_first_scale_r.
  rewrite (Hsource i Hi).

  apply Rinv_r.
 apply Rgt_not_eq.
apply Hpi.
exact Hi.
Qed.

Theorem marqsim_flow_transition_stochastic :
  forall n pi f,
    (forall i, (i < n)%nat -> 0 < pi i) ->
    marqsim_flow_nonnegative n f ->
    marqsim_flow_source_constraint n pi f ->
    marqsim_stochastic_kernel
      n
      (marqsim_flow_transition pi f).
Proof.
  intros n pi f Hpi Hnonneg Hsource.
  unfold marqsim_stochastic_kernel.
  intros i Hi.
  split.

  - intros j Hj.
    eapply marqsim_flow_transition_nonnegative; eauto.

  - eapply marqsim_flow_transition_row_sum; eauto.
Qed.

Lemma marqsim_flow_cancel_pi :
  forall pi f i j,
    pi i <> 0 ->
    pi i * marqsim_flow_transition pi f i j
    =
    f i j.
Proof.
  intros pi f i j Hnz.
  unfold marqsim_flow_transition.
  unfold Rdiv.

rewrite <- Rmult_assoc.
replace (pi i * f i j * / pi i)
  with ((pi i * / pi i) * f i j) by ring.

rewrite (Rinv_r (pi i) Hnz).
ring.
Qed.

Theorem marqsim_flow_network_preserves_stationary_distribution :
  forall n pi f,
    (forall i, (i < n)%nat -> 0 < pi i) ->
    marqsim_flow_sink_constraint n pi f ->
    marqsim_stationary_kernel
      n
      pi
      (marqsim_flow_transition pi f).
Proof.
  intros n pi f Hpi Hsink.
  unfold marqsim_stationary_kernel.
  intros j Hj.

  transitivity
    (marqsim_sum_first n (fun i => f i j)).

  - apply marqsim_sum_first_ext.
    intros i Hi.

    apply marqsim_flow_cancel_pi.
   intro Hzero.

assert (Hpos : 0 < pi i).
{
  apply Hpi.
  exact Hi.
}

rewrite Hzero in Hpos.
lra.

  - apply Hsink.
    exact Hj.
Qed.


Theorem marqsim_flow_network_correct :
  forall n pi f,
    (forall i, (i < n)%nat -> 0 < pi i) ->
    marqsim_flow_nonnegative n f ->
    marqsim_flow_source_constraint n pi f ->
    marqsim_flow_sink_constraint n pi f ->
    marqsim_stochastic_kernel
      n
      (marqsim_flow_transition pi f)
    /\
    marqsim_stationary_kernel
      n
      pi
      (marqsim_flow_transition pi f).
Proof.
  intros n pi f Hpi Hnonneg Hsource Hsink.
  split.

  - eapply marqsim_flow_transition_stochastic; eauto.

  - eapply marqsim_flow_network_preserves_stationary_distribution; eauto.
Qed.

(******************************************************************************)
(* Pointwise refinement of a list-based graph_transition to the flow-extracted *)
(* mathematical kernel.                                                        *)
(******************************************************************************)

Definition marqsim_graph_refines_flow
  (lp : lowprog)
  (graph_transition : nat -> list R)
  (f : marqsim_flow)
  : Prop :=
  forall i j,
    (i < marqsim_num_states lp)%nat ->
    (j < marqsim_num_states lp)%nat ->
    marqsim_graph_kernel graph_transition i j
    =
    marqsim_flow_transition (marqsim_pi lp) f i j.

Lemma marqsim_graph_stochastic_from_flow :
  forall lp graph_transition f,
    (forall i,
        (i < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp i) ->
    marqsim_flow_nonnegative
      (marqsim_num_states lp)
      f ->
    marqsim_flow_source_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->
    marqsim_graph_refines_flow
      lp graph_transition f ->
    marqsim_stochastic_kernel
      (marqsim_num_states lp)
      (marqsim_graph_kernel graph_transition).
Proof.
  intros lp graph_transition f
    Hpi Hnonneg Hsource Href.

  pose proof
    (marqsim_flow_transition_stochastic
       (marqsim_num_states lp)
       (marqsim_pi lp)
       f
       Hpi
       Hnonneg
       Hsource)
    as Hflow.

  unfold marqsim_stochastic_kernel in *.
  intros i Hi.

  specialize (Hflow i Hi).
  destruct Hflow as [Hflow_nonneg Hflow_sum].

  split.

  - intros j Hj.
    rewrite (Href i j Hi Hj).
    apply Hflow_nonneg.
    exact Hj.

  - transitivity
      (marqsim_sum_first
         (marqsim_num_states lp)
         (marqsim_flow_transition (marqsim_pi lp) f i)).

    + apply marqsim_sum_first_ext.
      intros j Hj.
      apply Href; assumption.

    + exact Hflow_sum.
Qed.

Lemma marqsim_graph_stationary_from_flow :
  forall lp graph_transition f,
    (forall i,
        (i < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp i) ->
    marqsim_flow_sink_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->
    marqsim_graph_refines_flow
      lp graph_transition f ->
    marqsim_stationary_kernel
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_graph_kernel graph_transition).
Proof.
  intros lp graph_transition f Hpi Hsink Href.

  pose proof
    (marqsim_flow_network_preserves_stationary_distribution
       (marqsim_num_states lp)
       (marqsim_pi lp)
       f
       Hpi
       Hsink)
    as Hflow.

  unfold marqsim_stationary_kernel in *.
  intros j Hj.

  transitivity
    (marqsim_sum_first
       (marqsim_num_states lp)
       (fun i =>
          marqsim_pi lp i
          *
          marqsim_flow_transition
            (marqsim_pi lp)
            f i j)).

  - apply marqsim_sum_first_ext.
    intros i Hi.
    rewrite (Href i j Hi Hj).
    reflexivity.

  - apply Hflow.
    exact Hj.
Qed.

(******************************************************************************)
(* Build the old QBlueMarQSimCorrect certificate from the actual flow-network  *)
(* constraints instead of assuming graph stationarity by hand.                 *)
(******************************************************************************)

Theorem QBlue_MarQSim_Correct_From_Flow_Network :
  forall lp alpha graph_transition f,

    marqsim_rows_well_formed
      lp graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_flow_nonnegative
      (marqsim_num_states lp)
      f ->

    marqsim_flow_source_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->

    marqsim_flow_sink_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->

    marqsim_graph_refines_flow
      lp graph_transition f ->

    QBlueMarQSimCorrect
      lp alpha graph_transition.
Proof.
  intros
    lp alpha graph_transition f
    Hrows Hprob Hpos Halpha
    Hflow_nonneg Hsource Hsink Href.

  constructor.

  - exact Hrows.

  - exact Hprob.

  - exact Hpos.

  - exact Halpha.

  - eapply marqsim_graph_stochastic_from_flow; eauto.

  - eapply marqsim_graph_stationary_from_flow; eauto.
Qed.

(******************************************************************************)
(* End-to-end structural theorem starting from the flow-network constraints.    *)
(******************************************************************************)

Theorem QBlue_MarQSim_Main_Correctness_From_Flow_Network :
  forall lp alpha graph_transition f,

    marqsim_rows_well_formed
      lp graph_transition ->

    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp) ->

    (forall k,
        (k < marqsim_num_states lp)%nat ->
        0 < marqsim_pi lp k) ->

    0 <= alpha < 1 ->

    marqsim_flow_nonnegative
      (marqsim_num_states lp)
      f ->

    marqsim_flow_source_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->

    marqsim_flow_sink_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f ->

    marqsim_graph_refines_flow
      lp graph_transition f ->

    MarQSimPaperConditions
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp alpha graph_transition).
Proof.
  intros
    lp alpha graph_transition f
    Hrows Hprob Hpos Halpha
    Hflow_nonneg Hsource Hsink Href.

  apply QBlue_MarQSim_Main_Correctness.

  eapply QBlue_MarQSim_Correct_From_Flow_Network; eauto.
Qed.

(******************************************************************************)
(*  Diamond-norm algebra                                               *)
(******************************************************************************)

Section MARQSIM_DIAMOND.

Variable nd : nat.
Definition MarQTransL := Matrix nd nd.

Variable norm_diamond : MarQTransL -> R.

Record MarQDiamondNormLaws : Prop := {
  marq_diamond_nonneg :
    forall A : MarQTransL,
      0 <= norm_diamond A;

  marq_diamond_I :
    norm_diamond (I nd) = 1;

  marq_diamond_triangle :
    forall A B : MarQTransL,
      norm_diamond (Mplus A B)
      <=
      norm_diamond A + norm_diamond B;

  marq_diamond_submultiplicative :
    forall A B : MarQTransL,
      norm_diamond (@Mmult nd nd nd A B)
      <=
      norm_diamond A * norm_diamond B
}.

Variable DL : MarQDiamondNormLaws.

Lemma marqsim_dianorm_pow_le :
  forall (A : MarQTransL) (k : nat),
    norm_diamond (Mmult_n k A)
    <=
    (norm_diamond A) ^ k.
Proof.
  intros A k.
  induction k as [|k IH].

  - simpl.
    rewrite (marq_diamond_I DL).
    lra.

  - simpl.
    eapply Rle_trans.

    + apply (marq_diamond_submultiplicative DL).

    + apply Rmult_le_compat_l.
      * apply (marq_diamond_nonneg DL).
      * exact IH.
Qed.

End MARQSIM_DIAMOND.


Definition marqsim_step_error_bound
  (lam t : R)
  (N : nat)
  : R :=
  (2 * lam * lam * t * t / (INR N * INR N))
  *
  exp (2 * lam * t / INR N).

Definition marqsim_total_error_bound
  (lam t : R)
  (N : nat)
  : R :=
  (2 * lam * lam * t * t / INR N)
  *
  exp (2 * lam * t / INR N).

Definition marqsim_paper_simplified_bound
  (lam t : R)
  (N : nat)
  : R :=
  2 * lam * lam * t * t / INR N.

Lemma marqsim_step_to_total_bound :
  forall lam t N,
    N <> 0%nat ->
    INR N * marqsim_step_error_bound lam t N
    =
    marqsim_total_error_bound lam t N.
Proof.
  intros lam t N HN.
  unfold marqsim_step_error_bound.
  unfold marqsim_total_error_bound.

  assert (HINR : INR N <> 0).
  {
    apply not_0_INR.
    exact HN.
  }

  unfold Rdiv.
rewrite Rinv_mult.

replace
  (INR N *
    (2 * lam * lam * t * t *
      (/ INR N * / INR N) *
      exp (2 * lam * t * / INR N)))
with
  ((INR N * / INR N) *
   (2 * lam * lam * t * t * / INR N *
    exp (2 * lam * t * / INR N)))
by ring.

rewrite (Rinv_r (INR N) HINR).
ring.
Qed.

Theorem marqsim_total_error_from_local_error :
  forall lam t N local total,
    N <> 0%nat ->
    local <= marqsim_step_error_bound lam t N ->
    total <= INR N * local ->
    total <= marqsim_total_error_bound lam t N.
Proof.
  intros lam t N local total HN Hlocal Htotal.

  assert (HN0 : 0 <= INR N).
  {
    apply pos_INR.
  }

  assert (HINRpos : 0 < INR N).
  {
    apply lt_0_INR.
    lia.
  }

  assert (HINR : INR N <> 0).
  {
    intro Hzero.
    rewrite Hzero in HINRpos.
    lra.
  }

  eapply Rle_trans with (r2 := INR N * local).

  - exact Htotal.

  - eapply Rle_trans
      with
        (r2 :=
           INR N *
           marqsim_step_error_bound lam t N).

    + apply Rmult_le_compat_l.
      * exact HN0.
      * exact Hlocal.

    + unfold marqsim_step_error_bound.
      unfold marqsim_total_error_bound.
      unfold Rdiv.

      rewrite Rinv_mult.

      replace
        (INR N *
         (2 * lam * lam * t * t *
          (/ INR N * / INR N) *
          exp (2 * lam * t * / INR N)))
      with
        ((INR N * / INR N) *
         (2 * lam * lam * t * t *
          / INR N *
          exp (2 * lam * t * / INR N)))
      by ring.

      rewrite (Rinv_r (INR N) HINR).
  rewrite Rmult_1_l.
apply Rle_refl.
Qed.

(******************************************************************************)
(* Error-budget theorem.                                                       *)
(******************************************************************************)

Theorem marqsim_error_budget_sound_exact :
  forall lam t eps N,
    0 < eps ->
    N <> 0%nat ->
    (2 * lam * lam * t * t *
       exp (2 * lam * t / INR N)) / eps
      <= INR N ->
    marqsim_total_error_bound lam t N <= eps.
Proof.
  intros lam t eps N Heps HN Hchoice.

  unfold marqsim_total_error_bound.

  assert (HNpos : 0 < INR N).
  {
    apply lt_0_INR.
    lia.
  }

  assert (HINR : INR N <> 0).
  {
    intro Hzero.
    rewrite Hzero in HNpos.
    lra.
  }

  assert (Heps_nz : eps <> 0).
  {
    intro Hzero.
    rewrite Hzero in Heps.
    lra.
  }

  (* Normalize division in the hypothesis. *)
  unfold Rdiv in Hchoice.

assert (Hmain :
  2 * lam * lam * t * t *
    exp (2 * lam * t * / INR N)
  <=
  INR N * eps).
{
  apply (Rmult_le_reg_r (/ eps)).

  - apply Rinv_0_lt_compat.
    exact Heps.

   - replace
      (INR N * eps * / eps)
    with
      (INR N).

    + exact Hchoice.

    + replace
        (INR N * eps * / eps)
      with
        (INR N * (eps * / eps))
      by ring.

      rewrite (Rinv_r eps Heps_nz).
      ring.

}
  (* Normalize division in the goal. *)
  unfold Rdiv.

  (* Multiply both sides by positive INR N. *)
apply (Rmult_le_reg_r (INR N)).

- exact HNpos.

- replace
    ((2 * lam * lam * t * t *
        / INR N *
        exp (2 * lam * t * / INR N)) *
     INR N)
  with
    (2 * lam * lam * t * t *
       exp (2 * lam * t * / INR N)).

  + replace (eps * INR N) with (INR N * eps) by ring.
    exact Hmain.

  + replace
      (2 * lam * lam * t * t * / INR N *
         exp (2 * lam * t * / INR N) * INR N)
    with
      ((INR N * / INR N) *
       (2 * lam * lam * t * t *
          exp (2 * lam * t * / INR N)))
    by ring.

    rewrite (Rinv_r (INR N) HINR).
    rewrite Rmult_1_l.
    reflexivity.
Qed.

(******************************************************************************)
(*   Theorem 4.1 interface                                                    *)

(******************************************************************************)

Record MarQSimAnalyticCertificate
  (lam t : R)
  (N : nat)
  (local_error total_error : R)
  : Prop := {

  marqsim_cert_local :
    local_error
    <=
    marqsim_step_error_bound lam t N;

  marqsim_cert_composition :
    total_error
    <=
    INR N * local_error
}.

Theorem QBlue_MarQSim_Approximation_Error_Bound :
  forall lam t N local_error total_error,

    N <> 0%nat ->

    MarQSimAnalyticCertificate
      lam t N local_error total_error ->

    total_error
    <=
    marqsim_total_error_bound lam t N.
Proof.
  intros
    lam t N local_error total_error
    HN Hcert.

  destruct Hcert as [Hlocal Hcomposition].

  eapply marqsim_total_error_from_local_error; eauto.
Qed.

Theorem QBlue_MarQSim_Approximation_Error_With_Budget :
  forall lam t eps N local_error total_error,

    0 < eps ->

    N <> 0%nat ->

    MarQSimAnalyticCertificate
      lam t N local_error total_error ->

    (2 * lam * lam * t * t *
       exp (2 * lam * t / INR N)) / eps
      <= INR N ->

    total_error <= eps.
Proof.
  intros
    lam t eps N local_error total_error
    Heps HN Hcert Hbudget.

  eapply Rle_trans.

  - eapply QBlue_MarQSim_Approximation_Error_Bound.
    + exact HN.
    + exact Hcert.

  - eapply marqsim_error_budget_sound_exact; eauto.
Qed.

(******************************************************************************)
(*  Package structural + flow-network + analytical correctness           *)

(******************************************************************************)

Record QBlueMarQSimFullCertificate
  (lp : lowprog)
  (alpha : R)
  (graph_transition : nat -> list R)
  (f : marqsim_flow)
  (t : R)
  (N : nat)
  (local_error total_error : R)
  : Prop := {

  marqsim_full_rows :
    marqsim_rows_well_formed
      lp graph_transition;

  marqsim_full_probability :
    marqsim_prob_vector
      (marqsim_num_states lp)
      (marqsim_pi lp);

  marqsim_full_positive_support :
    forall k,
      (k < marqsim_num_states lp)%nat ->
      0 < marqsim_pi lp k;

  marqsim_full_mix_range :
    0 <= alpha < 1;

  marqsim_full_flow_nonnegative :
    marqsim_flow_nonnegative
      (marqsim_num_states lp)
      f;

  marqsim_full_source_flow :
    marqsim_flow_source_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f;

  marqsim_full_sink_flow :
    marqsim_flow_sink_constraint
      (marqsim_num_states lp)
      (marqsim_pi lp)
      f;

  marqsim_full_graph_refinement :
    marqsim_graph_refines_flow
      lp graph_transition f;

  marqsim_full_N_nonzero :
    N <> 0%nat;

  marqsim_full_analytic :
    MarQSimAnalyticCertificate
      (marqsim_lambda lp)
      t
      N
      local_error
      total_error
}.

Theorem QBlue_MarQSim_Full_Certified_Correctness :
  forall
    lp alpha graph_transition f
    t N local_error total_error,

    QBlueMarQSimFullCertificate
      lp alpha graph_transition f
      t N local_error total_error ->

    MarQSimPaperConditions
      (marqsim_num_states lp)
      (marqsim_pi lp)
      (marqsim_executable_kernel
         lp alpha graph_transition)

    /\

    total_error
    <=
    marqsim_total_error_bound
      (marqsim_lambda lp)
      t
      N.
Proof.
  intros
    lp alpha graph_transition f
    t N local_error total_error
    HC.

  destruct HC as
    [Hrows
     Hprob
     Hpos
     Halpha
     Hflow_nonneg
     Hsource
     Hsink
     Href
     HN
     Hanalytic].

  split.

  - eapply
      QBlue_MarQSim_Main_Correctness_From_Flow_Network;
      eauto.

  - eapply
      QBlue_MarQSim_Approximation_Error_Bound;
      eauto.
Qed.
