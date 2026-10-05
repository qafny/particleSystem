(* Matrix norm for square matrices: the operator norm
     ||M|| = max |Mv| over vectors with |v| <= 1,
   built on the vector norm from QuantumLib's CauchySchwarz.v.
   QBlueProofUtility.v uses this as `norm`. *)
Require Import Reals Psatz.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.CauchySchwarz.

Local Open Scope R_scope.

(* ---- facts about the vector norm ---- *)

Lemma fst_inner_le : forall {n} (u v : Vector n), fst ⟨u, v⟩ <= norm u * norm v.
Proof.
  intros n u v.
  eapply Rle_trans; [apply Cmod_ge_fst | apply Cauchy_Schwartz_ver2].
Qed.

Lemma vnorm_triangle : forall {n} (u v : Vector n), norm (u .+ v) <= norm u + norm v.
Proof.
  intros n u v.
  assert (Hsq : norm (u .+ v) ^ 2 <= (norm u + norm v) ^ 2).
  { rewrite norm_squared.
    rewrite inner_product_plus_l, !inner_product_plus_r.
    simpl fst.
    rewrite <- (norm_squared u), <- (norm_squared v).
    pose proof (fst_inner_le u v).
    pose proof (fst_inner_le v u).
    nra. }
  pose proof (norm_ge_0 (u .+ v)).
  pose proof (norm_ge_0 u).
  pose proof (norm_ge_0 v).
  nra.
Qed.

(* |w|^2 = sum of |w_i|^2 *)
Lemma Cmod_sq_fst : forall c : C, fst (c^* * c)%C = Cmod c ^ 2.
Proof.
  intros [a b]. unfold Cmod, Cconj, Cmult. simpl.
  repeat rewrite Rmult_1_r. rewrite sqrt_sqrt by nra. ring.
Qed.

Lemma fst_inner_self : forall {n} (w : Vector n),
  fst ⟨w, w⟩ = big_sum (fun i => Cmod (w i 0%nat) ^ 2) n.
Proof.
  intros n w. unfold inner_product, Mmult, adjoint.
  rewrite Re_big_sum. apply big_sum_eq_bounded. intros. apply Cmod_sq_fst.
Qed.

Lemma Rsum_mult_const_r : forall (f : nat -> R) (c : R) n,
  big_sum (fun i => f i * c) n = big_sum f n * c.
Proof. intros f c n. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

(* row i of M (conjugated) as a vector, so (M v)_i = <mrow M i, v> *)
Definition mrow {n} (M : Square n) (i : nat) : Vector n := fun j _ => (M i j)^*.

Lemma Mmult_entry_inner : forall {n} (M : Square n) (v : Vector n) i,
  (M × v) i 0%nat = ⟨mrow M i, v⟩.
Proof.
  intros. unfold inner_product, Mmult, adjoint, mrow.
  apply big_sum_eq_bounded. intros. rewrite Cconj_involutive. reflexivity.
Qed.

(* a rough bound |Mv|^2 <= K |v|^2, just so the max below exists *)
Definition mbound {n} (M : Square n) : R := big_sum (fun i => norm (mrow M i) ^ 2) n.

Lemma mbound_nonneg : forall {n} (M : Square n), 0 <= mbound M.
Proof. intros. unfold mbound. apply Rsum_ge_0. intros. apply pow2_ge_0. Qed.

Lemma Mmult_norm_sq_le : forall {n} (M : Square n) (v : Vector n),
  norm (M × v) ^ 2 <= mbound M * norm v ^ 2.
Proof.
  intros n M v.
  rewrite norm_squared, fst_inner_self.
  unfold mbound. rewrite <- Rsum_mult_const_r.
  apply Rsum_le. intros i Hi.
  rewrite Mmult_entry_inner.
  pose proof (Cauchy_Schwartz_ver2 (mrow M i) v).
  pose proof (Cmod_ge_0 ⟨mrow M i, v⟩).
  pose proof (norm_ge_0 (mrow M i)). pose proof (norm_ge_0 v).
  nra.
Qed.

(* ---- the operator norm ---- *)

Definition opset {n} (M : Square n) (r : R) : Prop :=
  exists v : Vector n, norm v <= 1 /\ r = norm (M × v).

Lemma opset_bound : forall {n} (M : Square n), bound (opset M).
Proof.
  intros n M. exists (1 + mbound M). intros r [v [Hv ->]].
  pose proof (Mmult_norm_sq_le M v) as H.
  pose proof (norm_ge_0 v). pose proof (norm_ge_0 (M × v)).
  pose proof (mbound_nonneg M).
  assert (norm v ^ 2 <= 1) by nra.
  nra.
Qed.

Lemma norm_Zero_vec : forall {n}, norm (@Zero n 1) = 0.
Proof. intros. apply norm_zero_iff_zero; auto with wf_db. Qed.

Lemma opset_nonempty : forall {n} (M : Square n), exists r, opset M r.
Proof.
  intros n M. exists 0. exists Zero. split.
  - rewrite norm_Zero_vec. lra.
  - rewrite Mmult_0_r, norm_Zero_vec. reflexivity.
Qed.

Definition mnorm (n : nat) (M : Square n) : R :=
  proj1_sig (completeness (opset M) (opset_bound M) (opset_nonempty M)).

Lemma mnorm_lub : forall n (M : Square n), is_lub (opset M) (mnorm n M).
Proof.
  intros n M. unfold mnorm.
  destruct (completeness (opset M) (opset_bound M) (opset_nonempty M)) as [m Hm].
  exact Hm.
Qed.

Lemma mnorm_upper : forall n (M : Square n) (v : Vector n),
  norm v <= 1 -> norm (M × v) <= mnorm n M.
Proof. intros n M v Hv. apply (proj1 (mnorm_lub n M)). exists v. split; auto. Qed.

Lemma mnorm_least : forall n (M : Square n) (b : R),
  (forall v : Vector n, norm v <= 1 -> norm (M × v) <= b) -> mnorm n M <= b.
Proof.
  intros n M b H. apply (proj2 (mnorm_lub n M)).
  intros r [v [Hv ->]]. apply H. exact Hv.
Qed.

Lemma mnorm_nonneg : forall n (M : Square n), 0 <= mnorm n M.
Proof.
  intros n M. eapply Rle_trans; [| apply (mnorm_upper n M Zero)].
  - rewrite Mmult_0_r, norm_Zero_vec. lra.
  - rewrite norm_Zero_vec. lra.
Qed.

(* |Mv| <= ||M|| |v| for any v *)
Lemma mnorm_scaled_bound : forall n (M : Square n) (v : Vector n),
  norm (M × v) <= mnorm n M * norm v.
Proof.
  intros n M v.
  pose proof (norm_ge_0 v) as Hv0. pose proof (mnorm_nonneg n M) as HM0.
  destruct (Req_dec (norm v) 0) as [Hz | Hnz].
  - pose proof (Mmult_norm_sq_le M v) as H. rewrite Hz in H.
    pose proof (norm_ge_0 (M × v)).
    assert (norm (M × v) = 0) by nra. rewrite Hz. nra.
  - assert (Hpos : 0 < norm v) by lra.
    set (u := RtoC (/ norm v) .* v).
    assert (Hu : norm u = 1).
    { unfold u. rewrite norm_scale, Cmod_R, Rabs_right.
      - field. lra.
      - left. apply Rinv_0_lt_compat. exact Hpos. }
    assert (HMu : norm (M × u) <= mnorm n M) by (apply mnorm_upper; lra).
    unfold u in HMu. rewrite Mscale_mult_dist_r, norm_scale, Cmod_R, Rabs_right in HMu.
    + apply (Rmult_le_compat_r (norm v)) in HMu; [| lra].
      replace (/ norm v * norm (M × v) * norm v) with (norm (M × v)) in HMu by (field; lra).
      exact HMu.
    + left. apply Rinv_0_lt_compat. exact Hpos.
Qed.

(* ---- the norm laws used in the proofs ---- *)

Lemma mnorm_zero : forall d, mnorm d Zero = 0.
Proof.
  intros d. apply Rle_antisym; [| apply mnorm_nonneg].
  apply mnorm_least. intros v Hv. rewrite Mmult_0_l, norm_Zero_vec. lra.
Qed.

Lemma mnorm_triangle : forall n (A B : Square n),
  mnorm n (A .+ B) <= mnorm n A + mnorm n B.
Proof.
  intros n A B. apply mnorm_least. intros v Hv.
  rewrite Mmult_plus_distr_r.
  eapply Rle_trans; [apply vnorm_triangle |].
  apply Rplus_le_compat; apply mnorm_upper; exact Hv.
Qed.

Lemma mnorm_submult : forall n (A B : Square n),
  mnorm n (A × B) <= mnorm n A * mnorm n B.
Proof.
  intros n A B. apply mnorm_least. intros v Hv.
  rewrite Mmult_assoc.
  eapply Rle_trans; [apply mnorm_scaled_bound |].
  apply Rmult_le_compat_l; [apply mnorm_nonneg | apply mnorm_upper; exact Hv].
Qed.

Lemma mnorm_scale : forall n (c : R) (A : Square n),
  mnorm n (RtoC c .* A) = (Rabs c * mnorm n A)%R.
Proof.
  intros n c A.
  assert (Hle : forall (c' : R) (B : Square n), mnorm n (RtoC c' .* B) <= Rabs c' * mnorm n B).
  { intros c' B. apply mnorm_least. intros v Hv.
    rewrite Mscale_mult_dist_l, norm_scale, Cmod_R.
    apply Rmult_le_compat_l; [apply Rabs_pos | apply mnorm_upper; exact Hv]. }
  apply Rle_antisym; [apply Hle |].
  destruct (Req_dec c 0) as [Hc | Hc].
  - subst. rewrite Rabs_R0, Rmult_0_l. apply mnorm_nonneg.
  - assert (HA : A = RtoC (/ c) .* (RtoC c .* A)).
    { rewrite Mscale_assoc, <- RtoC_mult, Rinv_l by exact Hc. rewrite Mscale_1_l. reflexivity. }
    pose proof (Hle (/ c) (RtoC c .* A)) as H. rewrite <- HA in H.
    rewrite Rabs_inv in H.
    pose proof (Rabs_pos_lt c Hc).
    apply (Rmult_le_compat_l (Rabs c)) in H; [| lra].
    replace (Rabs c * (/ Rabs c * mnorm n (RtoC c .* A))) with (mnorm n (RtoC c .* A)) in H
      by (field; lra).
    exact H.
Qed.

(* the vector norm only reads entries (i, 0) with i < n *)
Lemma norm_col0_eq : forall {n} (w w' : Vector n),
  (forall i, (i < n)%nat -> w i 0%nat = w' i 0%nat) -> norm w = norm w'.
Proof.
  intros n w w' H. unfold norm. f_equal. rewrite !fst_inner_self.
  apply big_sum_eq_bounded. intros i Hi. rewrite H by exact Hi. reflexivity.
Qed.

Lemma Mmult_make_WF_col0 : forall {n} (M : Square n) (v : Vector n) i,
  (M × v) i 0%nat = (M × make_WF v) i 0%nat.
Proof.
  intros n M v i. unfold Mmult, make_WF.
  apply big_sum_eq_bounded. intros y Hy.
  rewrite (proj2 (Nat.ltb_lt y n) Hy). reflexivity.
Qed.

Lemma unitary_preserves_norm : forall {d} (m : Square d) (u : Vector d),
  WF_Matrix m -> WF_Matrix u -> m × (m †) = I d -> norm (m × u) = norm u.
Proof.
  intros d m u Hm Hu HU.
  assert (Hflip : (m †) × m = I d) by (apply Minv_flip; auto with wf_db).
  unfold norm. f_equal. f_equal.
  rewrite inner_product_adjoint_r, <- Mmult_assoc, Hflip, Mmult_1_l by exact Hu.
  reflexivity.
Qed.

Lemma norm_e0 : forall d, (0 < d)%nat -> norm (@e_i d 0) = 1.
Proof.
  intros d Hd. destruct d as [| d']; [lia |].
  unfold norm. rewrite fst_inner_self. rewrite <- sqrt_1. f_equal.
  apply big_sum_unique. exists 0%nat. repeat split.
  - lia.
  - unfold e_i. simpl. rewrite Cmod_1. ring.
  - intros x Hx Hne. unfold e_i.
    replace (x =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
    simpl. rewrite Cmod_0. ring.
Qed.

(* a unitary has norm 1. needs size >= 1: at size 0 the zero matrix is
   also the identity, and its norm is 0 *)
Lemma mnorm_unitary : forall d (m : Square d),
  WF_Matrix m -> (0 < d)%nat -> m × (m †) = I d -> mnorm d m = 1.
Proof.
  intros d m Hm Hd HU. apply Rle_antisym.
  - apply mnorm_least. intros v Hv.
    rewrite (norm_col0_eq (m × v) (m × make_WF v)) by (intros; apply Mmult_make_WF_col0).
    rewrite unitary_preserves_norm by auto with wf_db.
    rewrite <- norm_make_WF. exact Hv.
  - rewrite <- (norm_e0 d Hd) at 1.
    rewrite <- (unitary_preserves_norm m (@e_i d 0)) by auto with wf_db.
    apply mnorm_upper. rewrite norm_e0 by exact Hd. lra.
Qed.

(* at size 0 every matrix has norm 0 *)
Lemma mnorm_dim0 : forall (M : Square 0), mnorm 0 M = 0.
Proof.
  intros M. apply Rle_antisym; [| apply mnorm_nonneg].
  apply mnorm_least. intros v Hv.
  unfold norm. rewrite fst_inner_self. simpl. rewrite sqrt_0. lra.
Qed.

Lemma Mopp_adjoint :
  forall n (A : Square n),
    (Mopp A) † = Mopp (A †).
Proof.
  intros n A.
  unfold Mopp, adjoint.
  prep_matrix_equality.

  unfold scale, Cconj, Cmult.
  simpl.

  destruct (A y x) as [ar ai].
  simpl.
  f_equal;
  ring.
Qed.


Lemma Mminus_adjoint :
  forall n (A B : Square n),
    (Mminus A B) †
    =
    Mminus (A †) (B †).
Proof.
  intros n A B.

  unfold Mminus.
  rewrite Mplus_adjoint.
  rewrite Mopp_adjoint.

  reflexivity.
Qed.

Lemma Mopp_mult_l :
  forall m n o
         (A : Matrix m n)
         (B : Matrix n o),
    Mmult (Mopp A) B
    =
    Mopp (Mmult A B).
Proof.
  intros m n o A B.
  unfold Mopp.
  rewrite Mscale_mult_dist_l.
  reflexivity.
Qed.

Lemma Mopp_mult_r :
  forall m n o
         (A : Matrix m n)
         (B : Matrix n o),
    Mmult A (Mopp B)
    =
    Mopp (Mmult A B).
Proof.
  intros m n o A B.
  unfold Mopp.
  rewrite Mscale_mult_dist_r.
  reflexivity.
Qed.

Lemma channel_difference_decomp :
  forall n (U L rho : Square n),
    Mminus
      (Mmult U (Mmult rho (U †)))
      (Mmult L (Mmult rho (L †)))
    =
    Mplus
      (Mmult
         (Mminus U L)
         (Mmult rho (U †)))
      (Mmult
         L
         (Mmult rho
            (Mminus (U †) (L †)))).
Proof.
  intros n U L rho.

  unfold Mminus.

  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.

  rewrite Mopp_mult_l.

  (* rho × Mopp(L†) *)
  rewrite Mopp_mult_r.

  (* L × Mopp(rho × L†) *)
  rewrite Mopp_mult_r.

  lma.
Qed.

Lemma vnorm_dual_bound :
  forall n (x y : Vector n),
    norm y <= 1 ->
    Cmod ⟨y, x⟩ <= norm x.
Proof.
  intros n x y Hy.

  eapply Rle_trans.
  - apply Cauchy_Schwartz_ver2.
  - pose proof (norm_ge_0 x).
    nra.
Qed.

Lemma inner_product_adjoint_move :
  forall n (A : Square n) (u v : Vector n),
    ⟨u, (A †) × v⟩
    =
    ⟨A × u, v⟩.
Proof.
  intros n A u v.
  rewrite inner_product_adjoint_r.
  rewrite adjoint_involutive.
  reflexivity.
Qed.

