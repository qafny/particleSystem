Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueCompile.
Require Import QBlue.QBlueParTransJwt.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueTrotterProof.
Require Import QuantumLib.VecSet.
Local Open Scope R_scope.


Require Import List.
Import ListNotations.
Local Open Scope list_scope.

From SQIR Require Import SQIR. 

Local Open Scope matrix_scope.
(* The "no randomness" version: evolve rho by the full combined Hamiltonian,
   for the per-round time step s (= t/N -- the ordinary, un-boosted step). *)
Definition qdrift_round_ideal (d : nat) (s : R) (hlist : norm_prog) (rho : Square (2^d)) : Square (2^d) :=
  let U := expH (2^d) s (norm_prog2mat hlist d) in
  Mmult U (Mmult rho (U †)).

(* The actual QDrift round, averaged over its own randomness: pick term i with
   probability |amp_i|/lam, evolve rho by conjugating with exp(-i tau sign(amp_i) H_i). *)
Fixpoint qdrift_round (d : nat) (tau lam : R) (hlist : norm_prog) (rho : Square (2^d)) : Square (2^d) :=
  match hlist with
  | [] => Zero
  | (amp, f) :: rem =>
    let sgn := if Rltb amp R0 then (- R1)%R else R1 in
    let U := expH (2^d) tau (normten2mat sgn d f) in
    Mplus (scale (Rabs amp / lam)%R (Mmult U (Mmult rho (U †))))
          (qdrift_round d tau lam rem rho)
  end.

(* One QDrift round vs. the ideal evolution it stands in for. Campbell,
   "A random compiler for fast Hamiltonian simulation" (arXiv:1811.08017),
   App. B, Eq. (B10)-(B12): with tau = lam*t/N and lam = sum |h_j|, the
   diamond distance d = (1/2)||.|| of one round is at most
   2 tau^2 e^(2 tau) (his (2 lam^2 t^2 / N^2) e^(2 lam t / N)); we state the
   un-halved norm, hence the 4. Needs lam to really be the total weight, so
   the probabilities |amp|/lam sum to 1 -- without that the statement is false. *)
Axiom qdrift_round_bound : forall (d : nat) (tau lam : R) (hlist : norm_prog) (rho : Square (2^d)),
  lam > 0 ->
  lam = sum_w hlist (length hlist) ->
  WF_Matrix rho ->
  norm (2^d) rho <= 1 ->
  norm (2^d) (Mminus (qdrift_round d tau lam hlist rho)
                      (qdrift_round_ideal d (tau/lam) hlist rho))
  <= 4 * tau * tau * exp (2 * tau).



(* U x U† = I implies U† x U = I too, for a square matrix -- a one-sided
   inverse is automatically two-sided. QuantumLib's Minv_flip does the real
   work; this just packages it for expH specifically. *)
Lemma expH_adjoint_unitary : forall (n : nat) (t : R) (M : Square n),
  Mmult ((expH n t M) †) (expH n t M) = I n.
Proof.
  intros n t M.
  apply Minv_flip.
  - auto with wf_db.
  - auto with wf_db.
  - apply expH_unitary.
Qed.

Lemma Mscale_minus_distr : forall n (p : R) (X Y : Square n), Mminus (scale p X) (scale p Y) = scale p (Mminus X Y).
Proof. intros. lma. Qed.

Lemma qdrift_term_contract : forall (d : nat) (tau p : R) (M rho1 rho2 : Square (2^d)),
  norm (2^d) (Mminus (scale p (Mmult (expH (2^d) tau M) (Mmult rho1 ((expH (2^d) tau M) †))))
                      (scale p (Mmult (expH (2^d) tau M) (Mmult rho2 ((expH (2^d) tau M) †)))))
  <= Rabs p * norm (2^d) (Mminus rho1 rho2).
Proof.
  intros d tau p M rho1 rho2.
  rewrite Mscale_minus_distr.
  rewrite matnorm_scale.
  apply Rmult_le_compat_l.
  - apply Rabs_pos.
  - apply sandwich_diff_bound.
    + auto with wf_db.
    + auto with wf_db.
    + apply expH_unitary.
    + rewrite adjoint_involutive. apply expH_adjoint_unitary.
Qed.

Lemma qdrift_round_contract : forall (d : nat) (tau lam : R) (hlist : norm_prog) (rho1 rho2 : Square (2^d)),
  lam > 0 ->
  norm (2^d) (Mminus (qdrift_round d tau lam hlist rho1) (qdrift_round d tau lam hlist rho2))
  <= (sum_w hlist (length hlist) / lam) * norm (2^d) (Mminus rho1 rho2).
Proof.
  intros d tau lam hlist.
  induction hlist as [| [amp f] rem IH]; intros rho1 rho2 Hlam.
  - simpl.
    unfold Mminus. rewrite Mplus_opp_0.
    rewrite zero_norm_eqzero.
    right. unfold Rdiv. ring.
  - simpl.
    assert (Hsplit: forall (U : Square (2^d)),
      Mminus (Mplus (scale (Rabs amp / lam)%R (Mmult U (Mmult rho1 (U †)))) (qdrift_round d tau lam rem rho1))
             (Mplus (scale (Rabs amp / lam)%R (Mmult U (Mmult rho2 (U †)))) (qdrift_round d tau lam rem rho2))
    = Mplus (Mminus (scale (Rabs amp / lam)%R (Mmult U (Mmult rho1 (U †)))) (scale (Rabs amp / lam)%R (Mmult U (Mmult rho2 (U †)))))
            (Mminus (qdrift_round d tau lam rem rho1) (qdrift_round d tau lam rem rho2))).
    { intros U. unfold Mminus, Mopp. lma. }
    rewrite Hsplit.
    assert (Hb1: norm (2^d) (Mminus (scale (Rabs amp / lam)%R (Mmult (expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) (Mmult rho1 ((expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) †))))
                                    (scale (Rabs amp / lam)%R (Mmult (expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) (Mmult rho2 ((expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) †)))))
      <= Rabs (Rabs amp / lam) * norm (2^d) (Mminus rho1 rho2)).
    { apply qdrift_term_contract. }
    assert (Hb2: norm (2^d) (Mminus (qdrift_round d tau lam rem rho1) (qdrift_round d tau lam rem rho2))
      <= (sum_w rem (length rem) / lam) * norm (2^d) (Mminus rho1 rho2)).
    { apply IH. exact Hlam. }
    eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + eapply Rle_trans.
      * apply Rplus_le_compat; [exact Hb1 | exact Hb2].
      * rewrite Rabs_right by (unfold Rdiv; apply Rle_ge; apply Rmult_le_pos; [apply Rabs_pos | left; apply Rinv_0_lt_compat; exact Hlam]).
        right. unfold Rdiv. field. lra.
Qed.

Lemma expH_conj_norm_le : forall (n : nat) (t : R) (M rho : Square n),
  norm n (Mmult (expH n t M) (Mmult rho ((expH n t M) †))) <= norm n rho.
Proof.
  intros n t M rho.
  assert (HU: norm n (expH n t M) = 1).
  { apply unitarymat_norm_eqone. apply expH_unitary. }
  assert (HUd: norm n ((expH n t M) †) = 1).
  { apply unitarymat_norm_eqone. rewrite adjoint_involutive. apply expH_adjoint_unitary. }
  eapply Rle_trans.
  - apply matnorm_mult_triangle_ineq.
  - rewrite HU, Rmult_1_l.
    eapply Rle_trans.
    + apply matnorm_mult_triangle_ineq.
    + rewrite HUd, Rmult_1_r. apply Rle_refl.
Qed.

Lemma qdrift_round_ideal_norm_le : forall (d : nat) (s : R) (hlist : norm_prog) (rho : Square (2^d)),
  norm (2^d) (qdrift_round_ideal d s hlist rho) <= norm (2^d) rho.
Proof.
  intros d s hlist rho.
  unfold qdrift_round_ideal.
  apply expH_conj_norm_le.
Qed.



Lemma qdrift_round_norm_le : forall (d : nat) (tau lam : R) (hlist : norm_prog) (rho : Square (2^d)),
  lam > 0 ->
  norm (2^d) (qdrift_round d tau lam hlist rho) <= (sum_w hlist (length hlist) / lam) * norm (2^d) rho.
Proof.
  intros d tau lam hlist rho.
  induction hlist as [| [amp f] rem IH]; intros Hlam.
  - simpl.
    rewrite zero_norm_eqzero.
    assert (H0: (R0 / lam * norm (2^d) rho)%R = 0%R) by (unfold Rdiv; ring).
    rewrite H0. apply Rle_refl.

  - simpl.
     assert (Hb1: norm (2^d) (scale (Rabs amp / lam)%R (Mmult (expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) (Mmult rho ((expH (2^d) tau (normten2mat (if Rltb amp R0 then (-R1)%R else R1) d f)) †))))
                <= Rabs (Rabs amp / lam) * norm (2^d) rho).
    { rewrite matnorm_scale.
      apply Rmult_le_compat_l.
      - apply Rabs_pos.
      - apply expH_conj_norm_le. }
        assert (Hb2: norm (2^d) (qdrift_round d tau lam rem rho)
                <= (sum_w rem (length rem) / lam) * norm (2^d) rho).
    { apply IH. exact Hlam. }
        eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + eapply Rle_trans.
      * apply Rplus_le_compat; [exact Hb1 | exact Hb2].
      * rewrite Rabs_right by (unfold Rdiv; apply Rle_ge; apply Rmult_le_pos; [apply Rabs_pos | left; apply Rinv_0_lt_compat; exact Hlam]).
        right. unfold Rdiv. field. lra.
Qed.

Fixpoint qdrift_iter (d : nat) (tau lam : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)) : Square (2^d) :=
  match N with
  | 0 => rho
  | S N' => qdrift_round d tau lam hlist (qdrift_iter d tau lam hlist N' rho)
  end.

Fixpoint qdrift_ideal_iter (d : nat) (s : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)) : Square (2^d) :=
  match N with
  | 0 => rho
  | S N' => qdrift_round_ideal d s hlist (qdrift_ideal_iter d s hlist N' rho)
  end.

Lemma qdrift_ideal_iter_norm_le : forall (d : nat) (s : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)),
  norm (2^d) (qdrift_ideal_iter d s hlist N rho) <= norm (2^d) rho.
Proof.
  intros d s hlist N rho.
  induction N as [| N' IH].
  - simpl. apply Rle_refl.
  - simpl.
    eapply Rle_trans.
    + apply qdrift_round_ideal_norm_le.
    + exact IH.
Qed.

Lemma qdrift_ideal_iter_wf : forall (d : nat) (s : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)),
  WF_Matrix rho -> WF_Matrix (qdrift_ideal_iter d s hlist N rho).
Proof.
  intros d s hlist N rho Hwf.
  induction N as [| N' IH].
  - simpl. exact Hwf.
  - simpl. unfold qdrift_round_ideal. auto with wf_db.
Qed.

Lemma qdrift_iter_bound : forall (d : nat) (tau lam : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)),
  lam > 0 ->
  lam = sum_w hlist (length hlist) ->
  WF_Matrix rho ->
  norm (2^d) rho <= 1 ->
  norm (2^d) (Mminus (qdrift_iter d tau lam hlist N rho)
                      (qdrift_ideal_iter d (tau / lam) hlist N rho))
  <= INR N * (4 * tau * tau * exp (2 * tau)).
Proof.
  intros d tau lam hlist N rho Hlam Hsum Hwf Hn1.
  induction N as [| N' IH].
  - simpl.
    unfold Mminus. rewrite Mplus_opp_0.
    rewrite zero_norm_eqzero.
    rewrite Rmult_0_l. apply Rle_refl.
  - cbn [qdrift_iter qdrift_ideal_iter].
    rewrite S_INR.
    rewrite (Mminus_split (2^d) _
      (qdrift_round d tau lam hlist (qdrift_ideal_iter d (tau / lam) hlist N' rho)) _).
    eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + assert (Hc: norm (2^d) (Mminus (qdrift_round d tau lam hlist (qdrift_iter d tau lam hlist N' rho))
                                      (qdrift_round d tau lam hlist (qdrift_ideal_iter d (tau / lam) hlist N' rho)))
                  <= norm (2^d) (Mminus (qdrift_iter d tau lam hlist N' rho)
                                         (qdrift_ideal_iter d (tau / lam) hlist N' rho))).
      { eapply Rle_trans.
        - apply qdrift_round_contract. exact Hlam.
        - rewrite <- Hsum. unfold Rdiv. rewrite Rinv_r by lra.
          rewrite Rmult_1_l. apply Rle_refl. }
      assert (Hb: norm (2^d) (Mminus (qdrift_round d tau lam hlist (qdrift_ideal_iter d (tau / lam) hlist N' rho))
                                      (qdrift_round_ideal d (tau / lam) hlist (qdrift_ideal_iter d (tau / lam) hlist N' rho)))
                  <= 4 * tau * tau * exp (2 * tau)).
      { apply qdrift_round_bound.
        - exact Hlam.
        - exact Hsum.
        - apply qdrift_ideal_iter_wf. exact Hwf.
        - eapply Rle_trans.
          + apply qdrift_ideal_iter_norm_le.
          + exact Hn1. }
      eapply Rle_trans.
      * apply Rplus_le_compat; [exact Hc | exact Hb].
      * nra.
Qed.

Lemma qdrift_round_ideal_add : forall (d : nat) (s1 s2 : R) (hlist : norm_prog) (rho : Square (2^d)),
  WF_Matrix rho ->
  qdrift_round_ideal d s1 hlist (qdrift_round_ideal d s2 hlist rho)
  = qdrift_round_ideal d (s1 + s2) hlist rho.
Proof.
  intros d s1 s2 hlist rho Hwf.
  unfold qdrift_round_ideal.
  rewrite <- expH_add.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma qdrift_ideal_iter_full : forall (d : nat) (s : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)),
  WF_Matrix rho ->
  qdrift_ideal_iter d s hlist (S N) rho = qdrift_round_ideal d (INR (S N) * s) hlist rho.
Proof.
  intros d s hlist N rho Hwf.
  induction N as [| N' IH].
  - cbn [qdrift_ideal_iter].
    replace (INR 1 * s) with s by (simpl; ring).
    reflexivity.
  - assert (Hstep: qdrift_ideal_iter d s hlist (S (S N')) rho
                  = qdrift_round_ideal d s hlist (qdrift_ideal_iter d s hlist (S N') rho))
      by reflexivity.
    rewrite Hstep, IH.
    rewrite qdrift_round_ideal_add by exact Hwf.
    f_equal.
    rewrite (S_INR (S N')).
    ring.
Qed.

Theorem qdrift_error_bound : forall (d : nat) (tau lam t : R) (hlist : norm_prog) (N : nat) (rho : Square (2^d)),
  lam > 0 ->
  lam = sum_w hlist (length hlist) ->
  INR (S N) * (tau / lam) = t ->
  WF_Matrix rho ->
  norm (2^d) rho <= 1 ->
  norm (2^d) (Mminus (qdrift_iter d tau lam hlist (S N) rho)
                      (qdrift_round_ideal d t hlist rho))
  <= INR (S N) * (4 * tau * tau * exp (2 * tau)).
Proof.
  intros d tau lam t hlist N rho Hlam Hsum Ht Hwf Hn1.
  rewrite <- Ht.
  rewrite <- qdrift_ideal_iter_full by exact Hwf.
  apply qdrift_iter_bound; assumption.
Qed.












