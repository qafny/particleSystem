(*
  QBlueQdriftProof_2.v

  Axiom-free correctness/error analysis for QDrift.

*)

From Coq Require Import Reals List Psatz Lia.

Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueMatNorm.
Require Import QBlue.QBlueMatrixExp.
Require Import QBlue.QBlueHamiltonian.
Require Import QBlue.QBlueMatrixExp.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueQdrift_01.

Local Open Scope R_scope.


(* ================================================================ *)
(* 1. Sign of a QDrift Hamiltonian coefficient                      *)
(* ================================================================ *)
Definition qdrift_sign (amp : R) : R :=
  if Rlt_dec amp 0 then (-1)%R else 1.

Lemma Rabs_mul_qdrift_sign :
  forall amp,
    Rabs amp * qdrift_sign amp = amp.
Proof.
  intro amp.
  unfold qdrift_sign.
  destruct (Rlt_dec amp 0) as [Hneg | Hnneg].

  - rewrite Rabs_left by exact Hneg.
    ring.

  - rewrite Rabs_right by lra.
    ring.
Qed.


(* ================================================================ *)
(* 2. Scaling Pauli-string Hamiltonians                              *)
(* ================================================================ *)

Lemma lowprogten2mat_scale :
  forall (a : R) (c : C) n f,
    lowprogten2mat ((RtoC a) * c)%C n f
    =
    RtoC a .* lowprogten2mat c n f.
Proof.
  intros a c n f.
  induction n as [| n' IH].

  - cbn [lowprogten2mat].
    rewrite Mscale_assoc.
    reflexivity.

  - cbn [lowprogten2mat].
    rewrite IH.

    unfold kron, scale.
    prep_matrix_equality.
    ring.
Qed.


Lemma normten2mat_scale :
  forall (a b : R) n f,
    normten2mat (a * b) n f
    =
    RtoC a .* normten2mat b n f.
Proof.
  intros a b n f.
  unfold normten2mat.

  rewrite RtoC_mult.
  apply lowprogten2mat_scale.
Qed.


(* A useful special case: every real-amplitude term is a scaling
   of the corresponding unit-amplitude Pauli string. *)

Lemma normten2mat_as_scale :
  forall (amp : R) n f,
    normten2mat amp n f
    =
    RtoC amp .* normten2mat 1 n f.
Proof.
  intros amp n f.
  transitivity (normten2mat (amp * 1) n f).
  - f_equal.
    ring.
  - apply normten2mat_scale.
Qed.



(* ================================================================ *)
(* 3. QDrift signed term identity                                   *)
(* ================================================================ *)

Lemma qdrift_signed_term :
  forall (amp : R) n f,
    RtoC (Rabs amp)
      .* normten2mat (qdrift_sign amp) n f
    =
    normten2mat amp n f.
Proof.
  intros amp n f.

  rewrite normten2mat_as_scale.
  rewrite normten2mat_as_scale.

  rewrite Mscale_assoc.
  rewrite <- RtoC_mult.

  rewrite Rabs_mul_qdrift_sign.

 rewrite Mscale_1_l.
symmetry.
apply normten2mat_as_scale.
Qed.



(* Cleaner version using the scalar sign identity. *)

Lemma qdrift_signed_term' :
  forall (amp : R) n f,
    RtoC (Rabs amp) .* normten2mat (qdrift_sign amp) n f
    =
    normten2mat amp n f.
Proof.
  intros amp n f.

  rewrite normten2mat_as_scale.
  rewrite normten2mat_as_scale.
  rewrite Mscale_assoc.
  rewrite <- RtoC_mult.
  rewrite Rabs_mul_qdrift_sign.
rewrite Mscale_1_l.
symmetry.
apply normten2mat_as_scale.
Qed.


(* ================================================================ *)
(* 4. Division by lambda                                            *)
(* ================================================================ *)

Lemma qdrift_weighted_term :
  forall (amp lam : R) n f,
    lam <> 0 ->
    RtoC (Rabs amp / lam)
      .* normten2mat (qdrift_sign amp) n f
    =
    RtoC (/ lam)
      .* normten2mat amp n f.
Proof.
  intros amp lam n f Hlam.

  (* Separate |amp|/lam into (1/lam) * |amp|. *)
  replace (Rabs amp / lam)%R
    with ((/ lam) * Rabs amp)%R
    by (unfold Rdiv; ring).

  rewrite RtoC_mult.
  rewrite <- Mscale_assoc.

  (* |amp| * sign(amp) P = amp P. *)
  rewrite qdrift_signed_term.

  reflexivity.
Qed.



(* ================================================================ *)
(* 5. Weighted sum of QDrift Hamiltonians                           *)
(* ================================================================ *)

Fixpoint qdrift_weighted_hamiltonian
  (lam : R) (hlist : norm_prog) (d : nat)
  : Square (2^d) :=
  match hlist with
  | [] =>
      Zero

  | (amp, f) :: rem =>
      Mplus
        (RtoC (Rabs amp / lam)
           .* normten2mat (qdrift_sign amp) d f)
        (qdrift_weighted_hamiltonian lam rem d)
  end.

Theorem qdrift_weighted_hamiltonian_correct :
  forall lam hlist d,
    lam <> 0 ->
    qdrift_weighted_hamiltonian lam hlist d
    =
    RtoC (/ lam) .* norm_prog2mat hlist d.
Proof.
  intros lam hlist.
  induction hlist as [| [amp f] rem IH];
    intros d Hlam.

  - cbn [qdrift_weighted_hamiltonian norm_prog2mat].
    rewrite Mscale_0_r.
    reflexivity.

  - cbn [qdrift_weighted_hamiltonian norm_prog2mat].
    rewrite qdrift_weighted_term by exact Hlam.
    rewrite IH by exact Hlam.
lma.
Qed.



(* ================================================================ *)
(* 6. Probability normalization                                     *)
(* ================================================================ *)

Lemma qdrift_probabilities_normalized :
  forall lam hlist,
    lam > 0 ->
    lam = qdrift_sum_w hlist (length hlist) ->
    qdrift_prob_sum lam hlist = 1.
Proof.
  intros lam hlist Hlam Hsum.
  apply qdrift_prob_sum_one.
  - exact Hlam.
  - exact Hsum.
Qed.

Lemma qdrift_weighted_term_1 :
  forall (amp lam : R) n f,
    RtoC (Rabs amp / lam)
      .* normten2mat (qdrift_sign amp) n f
    =
    RtoC (/ lam)
      .* normten2mat amp n f.
Proof.
  intros amp lam n f.

  replace (Rabs amp / lam)%R
    with ((/ lam) * Rabs amp)%R
    by (unfold Rdiv; ring).

  rewrite RtoC_mult.
  rewrite <- Mscale_assoc.
  rewrite qdrift_signed_term.
  reflexivity.
Qed.

Theorem qdrift_weighted_hamiltonian_correct_1 :
  forall lam hlist d,
    qdrift_weighted_hamiltonian lam hlist d
    =
    RtoC (/ lam) .* norm_prog2mat hlist d.
Proof.
  intros lam hlist.
  induction hlist as [| [amp f] rem IH];
    intros d.

  - cbn [qdrift_weighted_hamiltonian norm_prog2mat].
    rewrite Mscale_0_r.
    reflexivity.

  - cbn [qdrift_weighted_hamiltonian norm_prog2mat].
    rewrite qdrift_weighted_term_1.
    rewrite IH.
    lma.
Qed.

(* ================================================================ *)
(* 7. Norm bounds for QDrift Hamiltonians                           *)
(* ================================================================ *)

Lemma pauli2mat_unitary :
  forall p,
    WF_Unitary (pauli2mat p).
Proof.
  intro p.
  destruct p.
  - apply σx_unitary.
  - apply σy_unitary.
  - apply σz_unitary.
  - apply id_unitary.
Qed.

Global Hint Resolve pauli2mat_unitary : unit_db.

Lemma lowprogten2mat_one_unitary :
  forall d f,
    WF_Unitary
      (lowprogten2mat C1 d f).
Proof.
  intros d f.
  induction d as [| d' IH].

  - cbn [lowprogten2mat].
    rewrite Mscale_1_l.
    apply id_unitary.

  - cbn [lowprogten2mat].
    apply kron_unitary.
    + apply pauli2mat_unitary.
    + exact IH.
Qed.
Lemma normten2mat_one_unitary :
  forall d f,
    WF_Unitary
      (normten2mat 1 d f).
Proof.
  intros d f.
  unfold normten2mat.
  change
    (WF_Unitary
       (lowprogten2mat C1 d f)).
  apply lowprogten2mat_one_unitary.
Qed.

Lemma normten2mat_one_mul_adjoint :
  forall d f,
    normten2mat 1 d f
      × ((normten2mat 1 d f) †)
    =
    I (2^d).
Proof.
  intros d f.

  pose proof (normten2mat_one_unitary d f) as HU.
  unfold WF_Unitary in HU.
  destruct HU as [_ HU].

  pose proof (hermitian_normten 1 d f) as HH.
  unfold is_hermitian_mat in HH.

  rewrite HH.
  rewrite HH in HU.
  exact HU.
Qed.
Lemma mnorm_normten2mat_one :
  forall d f,
    mnorm (2^d) (normten2mat 1 d f) = 1.
Proof.
  intros d f.
  apply mnorm_unitary.

  - apply wf_normten2mat.

  - induction d.
    + simpl. lia.
    + simpl. lia.

  - apply normten2mat_one_mul_adjoint.
Qed.

Lemma mnorm_normten2mat :
  forall amp d f,
    mnorm (2^d) (normten2mat amp d f)
    =
    Rabs amp.
Proof.
  intros amp d f.
  rewrite normten2mat_as_scale.
  rewrite mnorm_scale.
  rewrite mnorm_normten2mat_one.
  ring.
Qed.

Lemma mnorm_norm_prog2mat_le_sum_w :
  forall d hlist,
    mnorm (2^d) (norm_prog2mat hlist d)
    <=
    qdrift_sum_w hlist (length hlist).
Proof.
  intros d hlist.
  induction hlist as [| [amp f] rem IH].

  - cbn [norm_prog2mat].
    rewrite mnorm_zero.
    simpl.
    lra.

  - cbn [norm_prog2mat qdrift_sum_w].

    eapply Rle_trans.
    + apply mnorm_triangle.
    + rewrite mnorm_normten2mat.
      apply Rplus_le_compat_l.
      exact IH.
Qed.


Lemma mnorm_norm_prog2mat_le_lam :
  forall d hlist lam,
    lam = qdrift_sum_w hlist (length hlist) ->
    mnorm (2^d) (norm_prog2mat hlist d)
    <= lam.
Proof.
  intros d hlist lam Hlam.
  rewrite Hlam.
  apply mnorm_norm_prog2mat_le_sum_w.
Qed.

Lemma mnorm_normalized_hamiltonian_le_one :
  forall d hlist lam,
    lam > 0 ->
    lam = qdrift_sum_w hlist (length hlist) ->
    mnorm (2^d)
      (RtoC (/ lam) .* norm_prog2mat hlist d)
    <= 1.
Proof.
  intros d hlist lam Hlam Hsum.

  rewrite mnorm_scale.

  rewrite Rabs_right.
  2: {
    left.
    apply Rinv_0_lt_compat.
    exact Hlam.
  }

  pose proof
    (mnorm_norm_prog2mat_le_lam
       d hlist lam Hsum) as Hnorm.

  apply Rmult_le_compat_l with (r := / lam) in Hnorm.
  2: {
    left.
    apply Rinv_0_lt_compat.
    exact Hlam.
  }

  replace (/ lam * lam)%R with 1 in Hnorm.
  - exact Hnorm.
- symmetry.
  apply Rinv_l.
  lra.
Qed.



(* ================================================================ *)
(* 8. Exact matrix exponential via operator-norm convergence        *)
(*                                                                  *)
(* We do not assume an exact matrix exponential as an axiom.        *)
(* Instead, U is an exact exponential of A when the finite Taylor   *)
(* partial sums converge to U in the operator norm mnorm.            *)
(* ================================================================ *)


(* ---------------------------------------------------------------- *)
(* 8.1 Matrix-sequence convergence                                  *)
(* ---------------------------------------------------------------- *)

Definition matrix_seq_cv {n : nat}
  (F : nat -> Square n)
  (L : Square n) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists N : nat,
      forall k : nat,
        (N <= k)%nat ->
        mnorm n (Mminus (F k) L) < eps.


(* ---------------------------------------------------------------- *)
(* 8.2 Exact matrix exponential relation                            *)
(* ---------------------------------------------------------------- *)

Definition matrix_exp_exact {n : nat}
  (A U : Square n) : Prop :=
  matrix_seq_cv
    (fun N => matrix_exp_partial A N)
    U.


(* ---------------------------------------------------------------- *)
(* 8.3 Norm of matrix negation                                      *)
(* ---------------------------------------------------------------- *)

Lemma mnorm_opp :
  forall n (A : Square n),
    mnorm n
      (RtoC (-1) .* A)
    =
    mnorm n A.
Proof.
  intros n A.

  rewrite mnorm_scale.

  replace (Rabs (-1)) with 1.
  - ring.
  - rewrite Rabs_left.
    + ring.
    + lra.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.4 Swapping a matrix difference changes only its sign           *)
(* ---------------------------------------------------------------- *)

Lemma Mminus_swap :
  forall n (A B : Square n),
    Mminus A B
    =
    RtoC (-1) .* Mminus B A.
Proof.
  intros n A B.

  unfold Mminus.

  lma.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.5 Operator norm is symmetric under subtraction                 *)
(*                                                                  *)
(*             ||A - B|| = ||B - A||                                *)
(* ---------------------------------------------------------------- *)

Lemma mnorm_minus_sym :
  forall n (A B : Square n),
    mnorm n (Mminus A B)
    =
    mnorm n (Mminus B A).
Proof.
  intros n A B.

  rewrite Mminus_swap.
  rewrite mnorm_opp.

  reflexivity.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.6 Triangle inequality for differences                          *)
(*                                                                  *)
(*        ||A - C|| <= ||A - B|| + ||B - C||                        *)
(* ---------------------------------------------------------------- *)

Lemma mnorm_minus_triangle :
  forall n (A B C : Square n),
    mnorm n (Mminus A C)
    <=
    mnorm n (Mminus A B)
    +
    mnorm n (Mminus B C).
Proof.
  intros n A B C.

  assert (Hdecomp :
    Mminus A C
    =
    Mplus
      (Mminus A B)
      (Mminus B C)).
  {
    unfold Mminus.
    lma.
  }

  rewrite Hdecomp.

  apply mnorm_triangle.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.7 Shifting a convergent matrix sequence by two indices         *)
(* ---------------------------------------------------------------- *)

Lemma matrix_seq_cv_shift2 :
  forall n
         (F : nat -> Square n)
         (L : Square n),
    matrix_seq_cv F L ->
    matrix_seq_cv
      (fun N => F (S (S N)))
      L.
Proof.
  intros n F L Hcv.

  unfold matrix_seq_cv in Hcv |- *.

  intros eps Heps.

  specialize (Hcv eps Heps).

  destruct Hcv as [N HN].

  exists N.

  intros k Hk.

  apply HN.

  lia.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.8 Shifted convergence of exponential partial sums              *)
(* ---------------------------------------------------------------- *)

Lemma matrix_exp_exact_shift2 :
  forall n
         (A U : Square n),
    matrix_exp_exact A U ->
    matrix_seq_cv
      (fun N =>
         matrix_exp_partial A (S (S N)))
      U.
Proof.
  intros n A U Hexp.

  unfold matrix_exp_exact in Hexp.

  apply matrix_seq_cv_shift2.

  exact Hexp.
Qed.


(* ---------------------------------------------------------------- *)
(* 8.9 Eventual scalar remainder upper bound                        *)
(*                                                                  *)
(* scalar_exp_remainder x N converges to                            *)
(*                                                                  *)
(*                  exp x - 1 - x                                   *)
(*                                                                  *)
(* so eventually it is strictly below that limit + eps.             *)
(* ---------------------------------------------------------------- *)

Lemma scalar_exp_remainder_eventually_le :
  forall x eps,
    eps > 0 ->
    exists N : nat,
      forall k : nat,
        (N <= k)%nat ->
        scalar_exp_remainder x k
        <
        (exp x - 1 - x) + eps.
Proof.
  intros x eps Heps.

  pose proof
    (scalar_exp_remainder_cvg x)
    as Hcv.

  unfold Un_cv in Hcv.

  specialize (Hcv eps Heps).

  destruct Hcv as [N HN].

  exists N.

  intros k Hk.

  specialize (HN k Hk).

  unfold R_dist in HN.

  apply Rabs_def2 in HN.

  destruct HN as [Hupper _].

  lra.
Qed.




(* ---------------------------------------------------------------- *)
(* 8.10 Exact exponential second-order bound                        *)
(*                                                                  *)
(* ||U - (I + A)||                                                  *)
(*       <= exp(||A||) - 1 - ||A||                                 *)
(* ---------------------------------------------------------------- *)

Theorem matrix_exp_exact_second_order_bound :
  forall n
         (A U : Square n),
    WF_Matrix A ->
    matrix_exp_exact A U ->
    mnorm n
      (Mminus
         U
         (I n .+ A))
    <=
    exp (mnorm n A)
    - 1
    - mnorm n A.
Proof.
  intros n A U HA Hexp.

  set
    (r :=
       exp (mnorm n A)
       - 1
       - mnorm n A).

  (* Suppose the desired bound is false. *)
  apply Rnot_lt_le.

  intro Hbad.

  (* Choose epsilon from the positive gap. *)
  assert (Heps :
    0 <
    (mnorm n
       (Mminus U (I n .+ A))
     - r) / 3).
  {
    lra.
  }

  set
    (eps :=
       (mnorm n
          (Mminus U (I n .+ A))
        - r) / 3).

  assert (Heps_pos :
    eps > 0).
  {
    unfold eps.
    lra.
  }

  (* Exact matrix exponential convergence. *)
  pose proof
    (matrix_exp_exact_shift2
       n A U Hexp)
    as Hmatrix.

  unfold matrix_seq_cv in Hmatrix.

  specialize
    (Hmatrix eps Heps_pos).

  destruct Hmatrix as
    [Nm HNm].

  (* Scalar remainder convergence. *)
  pose proof
    (scalar_exp_remainder_eventually_le
       (mnorm n A)
       eps
       Heps_pos)
    as Hscalar.

  destruct Hscalar as
    [Ns HNs].

  (* Use one sufficiently large index for both convergences. *)
  set (N := Nat.max Nm Ns).

  assert (HNmN :
    (Nm <= N)%nat).
  {
    unfold N.
    apply Nat.le_max_l.
  }

  assert (HNsN :
    (Ns <= N)%nat).
  {
    unfold N.
    apply Nat.le_max_r.
  }

  specialize
    (HNm N HNmN).

  specialize
    (HNs N HNsN).

  (* Existing finite Taylor bound from QBlueMatrixExp.v. *)
  pose proof
    (matrix_exp_partial_second_order_bound
       n A N HA)
    as Hfinite.

  (* First convert the orientation of the convergence bound.

     HNm currently says:

       || partial_N - U || < eps

     but the triangle inequality below uses:

       || U - partial_N || < eps.
  *)
  assert (HNm' :
    mnorm n
      (Mminus
         U
         (matrix_exp_partial
            A (S (S N))))
    < eps).
  {
    rewrite mnorm_minus_sym.
    exact HNm.
  }

  (* Bound the finite partial sum relative to I + A. *)
  assert (Hpartial :
    mnorm n
      (Mminus
         (matrix_exp_partial
            A (S (S N)))
         (I n .+ A))
    < r + eps).
  {
    eapply Rle_lt_trans.

    - exact Hfinite.

    - unfold r.
      exact HNs.
  }

  (* Triangle inequality through the finite partial sum. *)
  pose proof
    (mnorm_minus_triangle
       n
       U
       (matrix_exp_partial
          A (S (S N)))
       (I n .+ A))
    as Htriangle.

  assert (Htotal :
    mnorm n
      (Mminus U (I n .+ A))
    <
    eps + (r + eps)).
  {
    eapply Rle_lt_trans.

    - exact Htriangle.

    - apply Rplus_lt_compat.
      + exact HNm'.
      + exact Hpartial.
  }

  (* eps = (||U-(I+A)|| - r)/3 makes Htotal impossible. *)
  unfold eps in Htotal.

  lra.
Qed.


(* ================================================================ *)
(* 9. Second-order bound for Hamiltonian evolution                  *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(* 9.1 Exact exponential for a scaled Hamiltonian                   *)
(* ---------------------------------------------------------------- *)

Definition exact_hamiltonian_exp
  {n : nat}
  (t : R)
  (H U : Square n) : Prop :=
  matrix_exp_exact
    (RtoC t .* H)
    U.


(* ---------------------------------------------------------------- *)
(* 9.2 First-order approximation of an exact exponential            *)
(* ---------------------------------------------------------------- *)

Lemma exact_hamiltonian_exp_second_order :
  forall n
         (t : R)
         (H U : Square n),
    WF_Matrix H ->
    exact_hamiltonian_exp t H U ->
    mnorm n
      (Mminus
         U
         (I n .+ (RtoC t .* H)))
    <=
    exp (Rabs t * mnorm n H)
    - 1
    - (Rabs t * mnorm n H).
Proof.
  intros n t H U HH Hexp.

  unfold exact_hamiltonian_exp in Hexp.

  pose proof
    (matrix_exp_exact_second_order_bound
       n
       (RtoC t .* H)
       U)
    as Hbound.

  assert (Hwf :
    WF_Matrix (RtoC t .* H)).
  {
    apply WF_scale.
    exact HH.
  }

  specialize (Hbound Hwf Hexp).

  rewrite mnorm_scale in Hbound.

  exact Hbound.
Qed.

Lemma mnorm_scale_complex :
  forall n (c : C) (A : Square n),
    mnorm n (c .* A)
    =
    Cmod c * mnorm n A.
Proof.
  intros n c A.

  assert (Hle :
    forall (c' : C) (B : Square n),
      mnorm n (c' .* B)
      <=
      Cmod c' * mnorm n B).
  {
    intros c' B.

    apply mnorm_least.
    intros v Hv.

    rewrite Mscale_mult_dist_l.
    rewrite norm_scale.

    apply Rmult_le_compat_l.

    - apply Cmod_ge_0.

    - apply mnorm_upper.
      exact Hv.
  }

  apply Rle_antisym.

  - apply Hle.

  - destruct (Ceq_dec c 0) as [Hc | Hc].

    + subst c.
      rewrite Cmod_0.
      rewrite Rmult_0_l.

      apply mnorm_nonneg.

    + assert (HA :
        A = (/ c) .* (c .* A)).
      {
        rewrite Mscale_assoc.

        replace ((/ c) * c)%C with C1.
        - rewrite Mscale_1_l.
          reflexivity.
        - symmetry.
  apply Cinv_l.
  exact Hc.
      }


pose proof
  (Hle ((/ c)%C) (c .* A))
  as H.

rewrite <- HA in H.

rewrite Cmod_inv in H by exact Hc.

      assert (HCpos :
        0 < Cmod c).
      {
        apply Cmod_gt_0.
        exact Hc.
      }

      apply
        (Rmult_le_compat_l (Cmod c))
        in H.
      2: {
        lra.
      }

      replace
        (Cmod c *
           (/ Cmod c *
              mnorm n (c .* A)))
        with
        (mnorm n (c .* A))
        in H.
      2: {
        field.
        lra.
      }

      exact H.
Qed.

(* ---------------------------------------------------------------- *)
(* 9.3 Physical Hamiltonian generator: -i t H                       *)
(* ---------------------------------------------------------------- *)

Definition hamiltonian_generator
  {n : nat}
  (t : R)
  (H : Square n) : Square n :=
  (((- Ci) * RtoC t)%C) .* H.

Lemma Cmod_minus_i :
  Cmod (- Ci) = 1.
Proof.
  rewrite Cmod_opp.
  unfold Ci, Cmod.
  simpl.
  replace (0 * (0 * 1) + 1 * (1 * 1))%R with 1 by ring.
  apply sqrt_1.
Qed.

Lemma mnorm_hamiltonian_generator :
  forall n t (H : Square n),
    mnorm n (hamiltonian_generator t H)
    =
    Rabs t * mnorm n H.
Proof.
  intros n t H.
  unfold hamiltonian_generator.
  rewrite mnorm_scale_complex.
  rewrite Cmod_mult.
  rewrite Cmod_minus_i.
  rewrite Cmod_R.
  ring.
Qed.


(* ---------------------------------------------------------------- *)
(* 9.4 Exact physical Hamiltonian evolution                         *)
(* ---------------------------------------------------------------- *)

Definition exact_hamiltonian_evolution
  {n : nat}
  (t : R)
  (H U : Square n) : Prop :=
  matrix_exp_exact
    (hamiltonian_generator t H)
    U.


(* ---------------------------------------------------------------- *)
(* 9.5 Second-order approximation of physical evolution             *)
(* ---------------------------------------------------------------- *)

Lemma exact_hamiltonian_evolution_second_order :
  forall n
         (t : R)
         (H U : Square n),
    WF_Matrix H ->
    exact_hamiltonian_evolution t H U ->
    mnorm n
      (Mminus
         U
         (I n .+ hamiltonian_generator t H))
    <=
    exp (Rabs t * mnorm n H)
    - 1
    - (Rabs t * mnorm n H).
Proof.
  intros n t H U HH Hexp.

  unfold exact_hamiltonian_evolution in Hexp.

  pose proof
    (matrix_exp_exact_second_order_bound
       n
       (hamiltonian_generator t H)
       U)
    as Hbound.

  assert (Hwf :
    WF_Matrix
      (hamiltonian_generator t H)).
  {
    unfold hamiltonian_generator.
    apply WF_scale.
    exact HH.
  }

  specialize (Hbound Hwf Hexp).

  rewrite mnorm_hamiltonian_generator in Hbound.

  exact Hbound.
Qed.

Lemma matrix_power_comm :
  forall n (A : Square n) k,
    WF_Matrix A ->
    A × matrix_power A k
    =
    matrix_power A k × A.
Proof.
  intros n A k HA.
  induction k as [| k' IH].

  - cbn [matrix_power].
    rewrite Mmult_1_l by exact HA.
    rewrite Mmult_1_r by exact HA.
    reflexivity.

  - cbn [matrix_power].

    (* A × (A × A^k) = (A × A^k) × A *)
    rewrite Mmult_assoc.

    (* Replace A × A^k by A^k × A. *)
    rewrite IH.

    (* Reassociate the RHS. *)
    rewrite <- Mmult_assoc.

    reflexivity.
Qed.
Lemma matrix_power_adjoint :
  forall n (A : Square n) k,
    WF_Matrix A ->
    (matrix_power A k) †
    =
    matrix_power (A †) k.
Proof.
  intros n A k HA.
  induction k as [| k' IH].

  - cbn [matrix_power].
    rewrite id_adjoint_eq.
    reflexivity.

  - cbn [matrix_power].
    rewrite Mmult_adjoint.
    rewrite IH.

    symmetry.
    apply matrix_power_comm.

    apply WF_adjoint.
    exact HA.
Qed.

Lemma matrix_exp_term_adjoint :
  forall n (A : Square n) k,
    WF_Matrix A ->
    (matrix_exp_term A k) †
    =
    matrix_exp_term (A †) k.
Proof.
  intros n A k HA.

  unfold matrix_exp_term.

  assert (Hpow :
    (matrix_power A k) †
    =
    matrix_power (A †) k).
  {
    apply matrix_power_adjoint.
    exact HA.
  }

  unfold scale, adjoint.
  prep_matrix_equality.

  pose proof
    (f_equal
       (fun M : Square n => M x y)
       Hpow)
    as Hxy.

  unfold adjoint in Hxy.
  simpl in Hxy.

  unfold RtoC, Cconj.
  simpl.

  unfold Cconj in Hxy.
  simpl in Hxy.

unfold Cmult.
simpl.

rewrite <- Hxy.

simpl.
f_equal.
ring.
  ring.
Qed.

Lemma matrix_exp_partial_adjoint :
  forall n (A : Square n) N,
    WF_Matrix A ->
    (matrix_exp_partial A N) †
    =
    matrix_exp_partial (A †) N.
Proof.
  intros n A N HA.
  induction N as [| N' IH].

  - cbn [matrix_exp_partial].
    apply matrix_exp_term_adjoint.
    exact HA.

  - cbn [matrix_exp_partial].

    rewrite Mplus_adjoint.
    rewrite IH.
    rewrite matrix_exp_term_adjoint by exact HA.

    reflexivity.
Qed.

Definition vec_conj {n : nat} (v : Vector n) : Vector n :=
  fun i j => (v i j)^*.

Lemma inner_product_vec_conj_self :
  forall n (v : Vector n),
    ⟨vec_conj v, vec_conj v⟩
    =
    ⟨v, v⟩.
Proof.
  intros n v.

  unfold vec_conj, inner_product, adjoint, Mmult.

  apply big_sum_eq_bounded.
  intros i Hi.

  unfold Cconj.
  simpl.
unfold Cmult.
simpl.
f_equal;
ring.
Qed.

Lemma norm_vec_conj :
  forall n (v : Vector n),
    norm (vec_conj v) = norm v.
Proof.
  intros n v.
  unfold norm.
  rewrite inner_product_vec_conj_self.
  reflexivity.
Qed.

Lemma Mscale_adjoint_complex :
  forall m n (c : C) (A : Matrix m n),
    (c .* A) †
    =
    (c^*) .* (A †).
Proof.
  intros m n c A.
  unfold scale, adjoint.
  prep_matrix_equality.

  unfold Cconj, Cmult.
  simpl.

  f_equal;
  ring.
Qed.
Lemma hamiltonian_generator_adjoint :
  forall n t (H : Square n),
    H † = H ->
    (hamiltonian_generator t H) †
    =
    RtoC (-1) .* hamiltonian_generator t H.
Proof.
  intros n t H HH.

  unfold hamiltonian_generator.
  unfold scale, adjoint.
  prep_matrix_equality.

  pose proof
    (f_equal
       (fun M : Square n => M x y)
       HH)
    as Hxy.

  unfold adjoint in Hxy.
  simpl in Hxy.

  assert (Hre :
    fst (H y x) = fst (H x y)).
  {
    pose proof (f_equal fst Hxy) as Hre0.
    simpl in Hre0.
    exact Hre0.
  }

  assert (Him :
    (- snd (H y x))%R = snd (H x y)).
  {
    pose proof (f_equal snd Hxy) as Him0.
    simpl in Him0.
    exact Him0.
  }

  unfold RtoC, Ci, Cconj, Cmult.
  simpl.

  rewrite Hre.

  assert (Him' :
    snd (H y x) = (- snd (H x y))%R).
  {
    lra.
  }

  rewrite Him'.

  f_equal;
  ring.
Qed.

Lemma first_order_hamiltonian_adjoint :
  forall n t (H : Square n),
    H † = H ->
    (I n .+ hamiltonian_generator t H) †
    =
    I n .+
      (RtoC (-1) .* hamiltonian_generator t H).
Proof.
  intros n t H HH.

  rewrite Mplus_adjoint.
  rewrite id_adjoint_eq.
  rewrite hamiltonian_generator_adjoint by exact HH.

  reflexivity.
Qed.

Lemma first_order_channel_expansion :
  forall n
         (A rho : Square n),
    WF_Matrix A ->
    WF_Matrix rho ->
    Mmult
      (I n .+ A)
      (Mmult rho (I n .+ (RtoC (-1) .* A)))
    =
    rho
    .+
    Mplus
      (Mmult A rho)
      (RtoC (-1) .* Mmult rho A)
    .+
    (RtoC (-1) .* Mmult A (Mmult rho A)).
Proof.
  intros n A rho HA Hrho.

  (* rho × (I - A) *)
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_1_r by exact Hrho.
  rewrite Mscale_mult_dist_r.

  (* (I + A) × (...) *)
  rewrite Mmult_plus_distr_r.

  (* Distribute I and A before eliminating I. *)
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_1_l by exact Hrho.

  rewrite Mmult_plus_distr_l.

  (* I × (rho × A) *)
  rewrite Mmult_1_l.
  2: {
    apply WF_scale.
    apply WF_mult.
    - exact Hrho.
    - exact HA.
  }

  (* A × rho and A × (rho × A) are now explicit. *)
  rewrite Mscale_mult_dist_r.

  lma.
Qed.

Lemma hamiltonian_generator_commutator :
  forall n t (H rho : Square n),
    Mplus
      (Mmult (hamiltonian_generator t H) rho)
      (RtoC (-1) .* Mmult rho (hamiltonian_generator t H))
    =
    (((- Ci) * RtoC t)%C)
      .* Mminus
           (Mmult H rho)
           (Mmult rho H).
Proof.
  intros n t H rho.

  unfold hamiltonian_generator.
  unfold Mminus.

  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.

  lma.
Qed.

Lemma physical_first_order_channel_expansion :
  forall n t (H rho : Square n),
    WF_Matrix H ->
    WF_Matrix rho ->
    Mmult
      (I n .+ hamiltonian_generator t H)
      (Mmult
         rho
         (I n .+
            (RtoC (-1) .* hamiltonian_generator t H)))
    =
    rho
    .+
    (((- Ci) * RtoC t)%C)
      .* Mminus
           (Mmult H rho)
           (Mmult rho H)
    .+
    (RtoC (-1) .*
       Mmult
         (hamiltonian_generator t H)
         (Mmult rho (hamiltonian_generator t H))).
Proof.
  intros n t H rho HH Hrho.

  assert (Hgen :
    WF_Matrix (hamiltonian_generator t H)).
  {
    unfold hamiltonian_generator.
    apply WF_scale.
    exact HH.
  }

  rewrite first_order_channel_expansion
    by assumption.

  rewrite hamiltonian_generator_commutator.

  reflexivity.
Qed.
Lemma mnorm_generator_rho_generator :
  forall n t
         (H rho : Square n),
    mnorm n H <= 1 ->
    mnorm n rho <= 1 ->
    mnorm n
      (Mmult
         (hamiltonian_generator t H)
         (Mmult rho (hamiltonian_generator t H)))
    <=
    Rabs t * Rabs t.
Proof.
  intros n t H rho HH Hrho.

  pose proof (mnorm_nonneg n H) as HH0.
  pose proof (mnorm_nonneg n rho) as Hrho0.
  pose proof (Rabs_pos t) as Ht0.

  eapply Rle_trans
    with
      (r2 :=
         mnorm n (hamiltonian_generator t H)
         *
         mnorm n
           (Mmult rho (hamiltonian_generator t H))).

  - apply mnorm_submult.

  - rewrite mnorm_hamiltonian_generator.

    assert (Hinner :
      mnorm n
        (Mmult rho (hamiltonian_generator t H))
      <=
      mnorm n rho *
      (Rabs t * mnorm n H)).
    {
      eapply Rle_trans
        with
          (r2 :=
             mnorm n rho *
             mnorm n (hamiltonian_generator t H)).

      - apply mnorm_submult.

      - rewrite mnorm_hamiltonian_generator.
        apply Rle_refl.
    }

    eapply Rle_trans
      with
        (r2 :=
           (Rabs t * mnorm n H)
           *
           (mnorm n rho *
              (Rabs t * mnorm n H))).

    + apply Rmult_le_compat_l.
      * apply Rmult_le_pos.
        -- exact Ht0.
        -- exact HH0.
      * exact Hinner.

    + assert (HHsq :
        mnorm n H * mnorm n H <= 1).
      {
        nra.
      }

      assert (Hprod :
        mnorm n H *
          (mnorm n rho * mnorm n H)
        <= 1).
      {
        eapply Rle_trans
          with (r2 := mnorm n H * mnorm n H).

        - apply Rmult_le_compat_l.
          + exact HH0.
      + nra.

        - exact HHsq.
      }

      replace
        (Rabs t * mnorm n H *
           (mnorm n rho *
              (Rabs t * mnorm n H)))
        with
        ((Rabs t * Rabs t) *
           (mnorm n H *
              (mnorm n rho * mnorm n H)))
        by ring.

      replace
        (Rabs t * Rabs t)
        with
        ((Rabs t * Rabs t) * 1)
        at 2
        by ring.

      apply Rmult_le_compat_l.

      * apply Rmult_le_pos;
        exact Ht0.

      * exact Hprod.
Qed.

Lemma mnorm_generator_rho_generator_tau :
  forall n tau
         (H rho : Square n),
    0 <= tau ->
    mnorm n H <= 1 ->
    mnorm n rho <= 1 ->
    mnorm n
      (Mmult
         (hamiltonian_generator tau H)
         (Mmult rho (hamiltonian_generator tau H)))
    <=
    tau * tau.
Proof.
  intros n tau H rho Htau HH Hrho.

  eapply Rle_trans
    with (r2 := Rabs tau * Rabs tau).

  - apply mnorm_generator_rho_generator.
    + exact HH.
    + exact Hrho.

- rewrite Rabs_right by lra.
  apply Rle_refl.
Qed.

Lemma mnorm_first_order_hamiltonian_le :
  forall n t (H : Square n),
    mnorm n H <= 1 ->
    mnorm n
      (I n .+ hamiltonian_generator t H)
    <=
    1 + Rabs t.
Proof.
  intros n t H HH.

  eapply Rle_trans
    with
      (r2 :=
         mnorm n (I n)
         +
         mnorm n (hamiltonian_generator t H)).

  - apply mnorm_triangle.

  - rewrite mnorm_hamiltonian_generator.

    assert (Ht0 : 0 <= Rabs t).
    {
      apply Rabs_pos.
    }

    assert (HH0 : 0 <= mnorm n H).
    {
      apply mnorm_nonneg.
    }

    assert (HI :
      mnorm n (I n) <= 1).
    {
      destruct n as [| n'].

      - rewrite mnorm_dim0.
        lra.

      - rewrite mnorm_unitary.
        + lra.

        + apply WF_I.

        + lia.

        + rewrite id_adjoint_eq.
          rewrite Mmult_1_l.
          * reflexivity.
          * apply WF_I.
    }

    assert (Hscale :
      Rabs t * mnorm n H <= Rabs t).
    {
      replace (Rabs t)
        with (Rabs t * 1) at 2
        by ring.

      apply Rmult_le_compat_l.
      - exact Ht0.
      - exact HH.
    }

    lra.
Qed.

(* ================================================================ *)
(* 10. Exact semantic QDrift                                        *)
(* ================================================================ *)

(* Exact evolution channel for one Hamiltonian. *)
Definition exact_evolution_channel
  {n : nat}
  (t : R)
  (H U rho : Square n) : Square n :=
  U × (rho × U†).


(* One exact QDrift branch. *)
Definition exact_qdrift_branch
  (d : nat)
  (tau : R)
  (amp : R)
  (f : nat -> paulimat)
  (rho U : Square (2^d))
  : Square (2^d) :=
  RtoC (Rabs amp)
    .*
    exact_evolution_channel
      tau
      (normten2mat (qdrift_sign amp) d f)
      U
      rho.


(* ================================================================ *)
(* Relational semantics of one exact QDrift round                   *)
(*                                                                  *)
(* This replaces the old semantic dependence on the finite          *)
(* 32-term expH approximation.                                      *)
(* ================================================================ *)

Inductive exact_qdrift_round
  (d : nat)
  (tau lam : R)
  (rho : Square (2^d))
  : norm_prog -> Square (2^d) -> Prop :=

| ExactQDriftNil :
    exact_qdrift_round
      d tau lam rho
      []
      Zero

| ExactQDriftCons :
    forall amp f rem
           U rem_result,

      exact_hamiltonian_evolution
        tau
        (normten2mat (qdrift_sign amp) d f)
        U ->

      exact_qdrift_round
        d tau lam rho
        rem
        rem_result ->

      exact_qdrift_round
        d tau lam rho
        ((amp, f) :: rem)
        (Mplus
           (RtoC (Rabs amp / lam)
              .*
              exact_evolution_channel
                tau
                (normten2mat (qdrift_sign amp) d f)
                U
                rho)
           rem_result).




Inductive exact_qdrift_round_ideal
  (d : nat)
  (s : R)
  (hlist : norm_prog)
  (rho : Square (2^d))
  : Square (2^d) -> Prop :=

| ExactQDriftIdeal :
    forall U,

      exact_hamiltonian_evolution
        s
        (norm_prog2mat hlist d)
        U ->

      exact_qdrift_round_ideal
        d s hlist rho
        (exact_evolution_channel
           s
           (norm_prog2mat hlist d)
           U
           rho).


Definition qdrift_first_order_channel
  (d : nat)
  (tau lam : R)
  (hlist : norm_prog)
  (rho : Square (2^d))
  : Square (2^d) :=
  rho .+
    (((- Ci) * RtoC (tau / lam))%C
       .* Mminus
            (Mmult (norm_prog2mat hlist d) rho)
            (Mmult rho (norm_prog2mat hlist d))).

Definition qdrift_branch_first_order
  (d : nat)
  (tau : R)
  (amp : R)
  (f : nat -> paulimat)
  (rho : Square (2^d))
  : Square (2^d) :=
  rho .+
    (((- Ci) * RtoC tau)%C
       .* Mminus
            (Mmult
               (normten2mat (qdrift_sign amp) d f)
               rho)
            (Mmult
               rho
               (normten2mat (qdrift_sign amp) d f))).

Fixpoint qdrift_first_order_sum
  (d : nat)
  (tau lam : R)
  (hlist : norm_prog)
  (rho : Square (2^d))
  : Square (2^d) :=
  match hlist with
  | [] =>
      Zero

  | (amp, f) :: rem =>
      Mplus
        (RtoC (Rabs amp / lam)
           .* qdrift_branch_first_order
                d tau amp f rho)
        (qdrift_first_order_sum
           d tau lam rem rho)
  end.

Lemma exact_hamiltonian_second_order_tau_bound :
  forall n tau (H U : Square n),

    0 <= tau ->
    WF_Matrix H ->
    mnorm n H <= 1 ->
    exact_hamiltonian_evolution tau H U ->

    mnorm n
      (Mminus
         U
         (I n .+ hamiltonian_generator tau H))
    <=
    (tau * tau / 2) * exp tau.
Proof.
  intros n tau H U Htau Hwf Hnorm HU.

  eapply Rle_trans.

  - apply exact_hamiltonian_evolution_second_order.
    + exact Hwf.
    + exact HU.

  - rewrite Rabs_right.
    2:{
      lra.
    }

    set (x := tau * mnorm n H).

    assert (Hx0 : 0 <= x).
    {
      unfold x.
      apply Rmult_le_pos.
      - exact Htau.
      - apply mnorm_nonneg.
    }

    assert (HxTau : x <= tau).
    {
      unfold x.
      pose proof (mnorm_nonneg n H) as Hnorm0.
      nra.
    }

    eapply Rle_trans.

    + apply exp_second_order_remainder_bound.
      exact Hx0.

    + assert (Hexp :
        exp x <= exp tau).
      {
        destruct (Req_dec x tau) as [Heq | Hneq].

        - rewrite Heq.
          apply Rle_refl.

        - assert (Hlt : x < tau).
          {
            lra.
          }

          apply Rlt_le.
          apply exp_increasing.
          exact Hlt.
      }

      assert (Hsq :
        x * x <= tau * tau).
      {
        nra.
      }

      assert (Hxcoef :
        0 <= x * x / 2).
      {
        nra.
      }

      assert (Hcoef :
        x * x / 2 <= tau * tau / 2).
      {
        apply Rmult_le_compat_r.

        - apply Rlt_le.
          apply Rinv_0_lt_compat.
          lra.

        - exact Hsq.
      }

      assert (Hexppos :
        0 <= exp tau).
      {
        apply Rlt_le.
        apply exp_pos.
      }

      eapply Rle_trans
        with (r2 := (x * x / 2) * exp tau).

      * apply Rmult_le_compat_l.

        -- exact Hxcoef.

        -- exact Hexp.

      * apply Rmult_le_compat_r.

        -- exact Hexppos.

        -- exact Hcoef.
Qed.

Lemma exact_evolution_channel_first_order_bound :
  forall n tau (H rho U : Square n),

    0 <= tau ->

    WF_Matrix H ->

    WF_Matrix rho ->

    H † = H ->

    mnorm n H <= 1 ->

    mnorm n rho <= 1 ->

    exact_hamiltonian_evolution tau H U ->

    mnorm n
      (Mminus
         (exact_evolution_channel tau H U rho)
         (rho .+
            (((- Ci) * RtoC tau)%C
               .* Mminus
                    (Mmult H rho)
                    (Mmult rho H))))
    <=
    2 * tau * tau * exp (2 * tau).
Proof.
  intros n tau H rho U
         Htau HwfH HwfRho Hherm
         HnormH HnormRho HU.

  set (A := hamiltonian_generator tau H).
  set (L := I n .+ A).

  (* ======================================================== *)
  (* 1. Second-order approximation of the exact evolution     *)
  (* ======================================================== *)

  assert (Hrem :
    mnorm n (Mminus U L)
    <=
    (tau * tau / 2) * exp tau).
  {
    unfold L, A.

    apply exact_hamiltonian_second_order_tau_bound.
    - exact Htau.
    - exact HwfH.
    - exact HnormH.
    - exact HU.
  }

  (* ======================================================== *)
  (* 2. Elementary norm facts                                *)
  (* ======================================================== *)

  assert (HnormH0 :
    0 <= mnorm n H).
  {
    apply mnorm_nonneg.
  }

  assert (HnormRho0 :
    0 <= mnorm n rho).
  {
    apply mnorm_nonneg.
  }

  assert (Hexp_tau_pos :
    0 <= exp tau).
  {
    apply Rlt_le.
    apply exp_pos.
  }

  assert (HtauH :
    tau * mnorm n H <= tau).
  {
    nra.
  }

  (* ======================================================== *)
  (* 3. Norm of the Hamiltonian generator                     *)
  (* ======================================================== *)

  assert (HnormA :
    mnorm n A <= tau).
  {
    unfold A.

    rewrite mnorm_hamiltonian_generator.
rewrite Rabs_right.
- exact HtauH.
- lra.
  }

  assert (HnormA0 :
    0 <= mnorm n A).
  {
    apply mnorm_nonneg.
  }

  (* ======================================================== *)
  (* 4. Norm of the linear approximation L = I + A            *)
  (* ======================================================== *)

  assert (HnormL :
    mnorm n L <= 1 + tau).
  {
    unfold L.

    eapply Rle_trans.

    - apply mnorm_triangle.

    - assert (HI :
        mnorm n (I n) <= 1).
      {
        destruct n as [|n'].

        - rewrite mnorm_dim0.
          lra.

        - rewrite mnorm_unitary.
          + lra.
          + apply WF_I.
    + apply Nat.lt_0_succ.
+ rewrite id_adjoint_eq.
apply Mmult_1_l.
apply WF_I.
      }

      nra.
  }

  (* ======================================================== *)
  (* 5. Adjoint of A                                          *)
  (*                                                        *)
  (* A = -i tau H and H† = H, hence A† = -A.                *)
  (* ======================================================== *)

  assert (HAadj :
    A † = Mopp A).
  {
    unfold A, hamiltonian_generator.

    rewrite scale_adjoint.
    rewrite Hherm.

    apply functional_extensionality.
    intro i.
    apply functional_extensionality.
    intro j.

    unfold Mopp, scale.
    simpl.

    destruct (H i j) as [a b].
    simpl.
unfold Cconj, Cmult, Copp.
simpl.
f_equal.
- ring.
- ring.
  }

  (* ======================================================== *)
  (* 6. Adjoint of L                                          *)
  (*                                                        *)
  (* L† = I - A.                                             *)
  (* ======================================================== *)

  assert (HLadj :
    L † = I n .+ Mopp A).
  {
    unfold L.

    rewrite Mplus_adjoint.
   rewrite id_adjoint_eq.
rewrite HAadj.
reflexivity.
  }

  (* ======================================================== *)
  (* 7. Norm of U                                             *)
  (*                                                        *)
  (* Exact Hamiltonian evolution is unitary.                 *)
  (*                                                        *)
  (* If your exact evolution relation already has a          *)
  (* unitarity theorem, use it here.                          *)
  (* ======================================================== *)
assert (HnormU :
  mnorm n U
  <=
  1 + tau + (tau * tau / 2) * exp tau).
{
  eapply Rle_trans.

  - (* ||U|| <= ||U-L|| + ||L|| *)
   assert (HUdecomp :
  U = Mplus (Mminus U L) L).
{
  apply functional_extensionality.
  intro i.
  apply functional_extensionality.
  intro j.

  unfold Mplus, Mminus, Mopp, scale.
  simpl.

  destruct (U i j) as [ur ui] eqn:HUij.
  destruct (L i j) as [lr li] eqn:HLij.
unfold Mplus.
simpl.
  rewrite HUij.
  rewrite HLij.

  unfold Cplus, Cmult.
  simpl.

  f_equal.
  - ring.
  - ring.
}


  (* ======================================================== *)
  (* 8. Bound ||U† - L†||                                    *)
  (* ======================================================== *)

assert (Hrem_adj :
  mnorm n (Mminus (U †) (L †))
  <=
  (tau * tau / 2) * exp tau).
{
  eapply Rle_trans.

  - (* ||U|| <= ||U-L|| + ||L|| *)
   assert (HUdecomp :
  U = Mplus (Mminus U L) L).
{
  apply functional_extensionality.
  intro i.
  apply functional_extensionality.
  intro j.

  unfold Mplus, Mminus, Mopp, scale.
  simpl.

  destruct (U i j) as [ur ui] eqn:HUij.
  destruct (L i j) as [lr li] eqn:HLij.
unfold Mplus.
simpl.
  rewrite HUij.
  rewrite HLij.

  unfold Cplus, Cmult.
  simpl.

  f_equal.
  - ring.
  - ring.
}
Qed.

Lemma qdrift_branch_first_order_bound :
  forall d tau amp f rho U,

    0 <= tau ->

    WF_Matrix rho ->

    mnorm (2^d) rho <= 1 ->

    exact_hamiltonian_evolution
      tau
      (normten2mat (qdrift_sign amp) d f)
      U ->

    mnorm (2^d)
      (Mminus
         (exact_evolution_channel
            tau
            (normten2mat (qdrift_sign amp) d f)
            U
            rho)
         (qdrift_branch_first_order
            d tau amp f rho))
    <=
    2 * tau * tau * exp (2 * tau).
Proof.
  intros d tau amp f rho U
         Htau HrhoWF Hrho HU.

  unfold qdrift_branch_first_order.

  eapply exact_evolution_channel_first_order_bound.

  - exact Htau.

{
  eapply Rle_trans.

  - (* ||U|| <= ||U-L|| + ||L|| *)
   assert (HUdecomp :
  U = Mplus (Mminus U L) L).
{
  apply functional_extensionality.
  intro i.
  apply functional_extensionality.
  intro j.

  unfold Mplus, Mminus, Mopp, scale.
  simpl.

  destruct (U i j) as [ur ui] eqn:HUij.
  destruct (L i j) as [lr li] eqn:HLij.
unfold Mplus.
simpl.
  rewrite HUij.
  rewrite HLij.

  unfold Cplus, Cmult.
  simpl.

  f_equal.
  - ring.
  - ring.
}
Qed.


(* ================================================================ *)
(* Temporary bridge lemmas for the QDrift one-round proof           *)
(* ================================================================ *)

(* The weighted sum of the first-order branch approximations is
   exactly the global first-order QDrift channel. *)
Lemma qdrift_first_order_sum_correct :
  forall d tau lam hlist rho,

    lam > 0 ->

    lam =
      qdrift_sum_w hlist (length hlist) ->

    qdrift_first_order_sum
      d tau lam hlist rho
    =
    qdrift_first_order_channel
      d tau lam hlist rho.
Proof.
  intros d tau amp f rho U
         Htau HrhoWF Hrho HU.

  unfold qdrift_branch_first_order.

  eapply exact_evolution_channel_first_order_bound.

  - exact Htau.

{
  eapply Rle_trans.

  - (* ||U|| <= ||U-L|| + ||L|| *)
   assert (HUdecomp :
  U = Mplus (Mminus U L) L).
{
  apply functional_extensionality.
  intro i.
  apply functional_extensionality.
  intro j.

  unfold Mplus, Mminus, Mopp, scale.
  simpl.

  destruct (U i j) as [ur ui] eqn:HUij.
  destruct (L i j) as [lr li] eqn:HLij.
unfold Mplus.
simpl.
  rewrite HUij.
  rewrite HLij.

  unfold Cplus, Cmult.
  simpl.

  f_equal.
  - ring.
  - ring.
}
Qed.


(* The exact QDrift round is close to the weighted sum of the
   first-order branch approximations. *)
Lemma exact_qdrift_round_first_order_sum_bound :
  forall d tau lam hlist rho actual,

    0 <= tau ->

    lam > 0 ->

    lam =
      qdrift_sum_w hlist (length hlist) ->

    WF_Matrix rho ->

    mnorm (2^d) rho <= 1 ->

    exact_qdrift_round
      d tau lam rho hlist actual ->

    mnorm (2^d)
      (Mminus
         actual
         (qdrift_first_order_sum
            d tau lam hlist rho))
    <=
    2 * tau * tau * exp (2 * tau).
Proof.
  intros d tau amp f rho U
         Htau HrhoWF Hrho HU.

  unfold qdrift_branch_first_order.

  eapply exact_evolution_channel_first_order_bound.

  - exact Htau.

{
  eapply Rle_trans.

  - (* ||U|| <= ||U-L|| + ||L|| *)
   assert (HUdecomp :
  U = Mplus (Mminus U L) L).
{
  apply functional_extensionality.
  intro i.
  apply functional_extensionality.
  intro j.

  unfold Mplus, Mminus, Mopp, scale.
  simpl.

  destruct (U i j) as [ur ui] eqn:HUij.
  destruct (L i j) as [lr li] eqn:HLij.
unfold Mplus.
simpl.
  rewrite HUij.
  rewrite HLij.

  unfold Cplus, Cmult.
  simpl.

  f_equal.
  - ring.
  - ring.
}
Qed.


(* Combine the previous two results. *)
Lemma exact_qdrift_round_first_order_bound :
  forall d tau lam hlist rho actual,

    0 <= tau ->

    lam > 0 ->

    lam =
      qdrift_sum_w hlist (length hlist) ->

    WF_Matrix rho ->

    mnorm (2^d) rho <= 1 ->

    exact_qdrift_round
      d tau lam rho hlist actual ->

    mnorm (2^d)
      (Mminus
         actual
         (qdrift_first_order_channel
            d tau lam hlist rho))
    <=
    2 * tau * tau * exp (2 * tau).
Proof.
  intros d tau lam hlist rho actual
         Htau Hlam Hsum Hwf Hrho Hactual.

  rewrite <-
    (qdrift_first_order_sum_correct
       d tau lam hlist rho Hlam Hsum).

  eapply exact_qdrift_round_first_order_sum_bound.
  - exact Htau.
  - exact Hlam.
  - exact Hsum.
  - exact Hwf.
  - exact Hrho.
  - exact Hactual.
Qed.

Lemma exact_qdrift_ideal_first_order_bound :
  forall d tau lam hlist rho ideal,

    0 <= tau ->

    lam > 0 ->

    lam =
      qdrift_sum_w hlist (length hlist) ->

    WF_Matrix rho ->

    mnorm (2^d) rho <= 1 ->

    exact_qdrift_round_ideal
      d (tau / lam) hlist rho ideal ->

    mnorm (2^d)
      (Mminus
         ideal
         (qdrift_first_order_channel
            d tau lam hlist rho))
    <=
    2 * tau * tau * exp (2 * tau).
Proof.
  intros d tau lam hlist rho actual ideal
         Htau Hlam Hsum Hwf Hrho
         Hactual Hideal.


  set (H :=
    norm_prog2mat hlist d).

  set (s := tau / lam).

  set (first_order :=
    rho .+
      (((- Ci) * RtoC s)%C
         .* Mminus
              (Mmult H rho)
              (Mmult rho H))).


  assert (Hactual_bound :
    mnorm (2^d)
      (Mminus actual first_order)
    <=
    2 * tau * tau * exp (2 * tau)).
  {
    unfold first_order, H, s.

    eapply exact_qdrift_round_first_order_bound.

    - exact Htau.
    - exact Hlam.
    - exact Hsum.
    - exact Hwf.
    - exact Hrho.
    - exact Hactual.
  }


  assert (Hideal_bound :
    mnorm (2^d)
      (Mminus ideal first_order)
    <=
    2 * tau * tau * exp (2 * tau)).
  {
    unfold first_order, H, s.

    eapply exact_qdrift_ideal_first_order_bound.

    - exact Htau.
    - exact Hlam.
    - exact Hsum.
    - exact Hwf.
    - exact Hrho.
    - exact Hideal.
  }

  assert (Hdecomp :
    Mminus actual ideal
    =
    Mplus
      (Mminus actual first_order)
      (Mminus first_order ideal)).
  {
    unfold Mminus.
    lma.
  }

  rewrite Hdecomp.

  eapply Rle_trans.

  - apply mnorm_triangle.


    assert (Hsym :
      mnorm (2^d)
        (Mminus first_order ideal)
      =
      mnorm (2^d)
        (Mminus ideal first_order)).
    {

      apply mnorm_minus_sym.
    }

    rewrite Hsym.

    eapply Rle_trans.
    + apply Rplus_le_compat.
      * exact Hactual_bound.
      * exact Hideal_bound.

    + nra.
Qed.

Theorem qdrift_round_bound :
  forall (d : nat)
         (tau lam : R)
         (hlist : norm_prog)
         (rho actual ideal : Square (2^d)),

    0 <= tau ->

    lam > 0 ->

    lam = qdrift_sum_w hlist (length hlist) ->

    WF_Matrix rho ->

    mnorm (2^d) rho <= 1 ->

    exact_qdrift_round
      d tau lam rho hlist actual ->

    exact_qdrift_round_ideal
      d (tau / lam) hlist rho ideal ->

    mnorm (2^d)
      (Mminus actual ideal)
    <=
    4 * tau * tau * exp (2 * tau).
Proof.
  intros d tau lam hlist rho actual ideal
         Htau Hlam Hsum Hwf Hrho
         Hactual Hideal.


  set (H :=
    norm_prog2mat hlist d).

  set (s := tau / lam).

  set (first_order :=
    rho .+
      (((- Ci) * RtoC s)%C
         .* Mminus
              (Mmult H rho)
              (Mmult rho H))).



  assert (Hactual_bound :
    mnorm (2^d)
      (Mminus actual first_order)
    <=
    2 * tau * tau * exp (2 * tau)).
  {
    unfold first_order, H, s.

    eapply exact_qdrift_round_first_order_bound.

    - exact Htau.
    - exact Hlam.
    - exact Hsum.
    - exact Hwf.
    - exact Hrho.
    - exact Hactual.
  }


  assert (Hideal_bound :
    mnorm (2^d)
      (Mminus ideal first_order)
    <=
    2 * tau * tau * exp (2 * tau)).
  {
    unfold first_order, H, s.

    eapply exact_qdrift_ideal_first_order_bound.

    - exact Htau.
    - exact Hlam.
    - exact Hsum.
    - exact Hwf.
    - exact Hrho.
    - exact Hideal.
  }


  assert (Hdecomp :
    Mminus actual ideal
    =
    Mplus
      (Mminus actual first_order)
      (Mminus first_order ideal)).
  {
    unfold Mminus.
    lma.
  }

  rewrite Hdecomp.

  eapply Rle_trans.

  - apply mnorm_triangle.

  - (* use ||first_order - ideal|| = ||ideal - first_order|| *)
    assert (Hsym :
      mnorm (2^d)
        (Mminus first_order ideal)
      =
      mnorm (2^d)
        (Mminus ideal first_order)).
    {
      (* Requires the elementary norm symmetry ||A-B||=||B-A||. *)
      apply mnorm_minus_sym.
    }

    rewrite Hsym.

    eapply Rle_trans.
    + apply Rplus_le_compat.
      * exact Hactual_bound.
      * exact Hideal_bound.

    + nra.
Qed.


