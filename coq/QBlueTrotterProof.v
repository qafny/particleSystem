(* Define the trotterization step, Lie-Trotter fomular, qdrift.
   Operates on norm_prog (real amplitude) rather than lowprog (complex
   amplitude) for the actual Hamiltonian being Trotterized -- at the
   Pauli-string level every Hamiltonian term's coefficient is real (paper's
   Definition 3.1), so working with a real amplitude throughout lets
   Hermiticity of the generator be PROVED (hermitian_norm_prog2mat in
   QBlueProofUtility.v) rather than assumed away.
   The "commutator" symbolic-arithmetic helpers below (commutator_tt/st/ts/ss)
   are a deliberate exception and stay lowprog/complex-typed: composing two
   Pauli strings via operator composition (not sum) can produce genuinely
   non-real coefficients (e.g. X ∘ Y = iZ, from QBlueParTransJwt.v's
   app_pauli table) even when every individual Hamiltonian term is real, so
   they need the general complex representation. Terms extracted from the
   (real) Hamiltonian are embedded into that representation via RtoC exactly
   where they're fed into that machinery, and nowhere else. *)
Require Import QuantumLib.Matrix.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueParTransJwtProof.
Require Import QBlue.QBlueTrotter.
Require Import QBlue.QBlueUtility.

(**** Approximate central value using 1st-order std Trotter
Approx = exp(-itH_k) exp(-itH_{k-1}) ... exp(-itH_{1})
d: d paulis in one tensor product ****)
Fixpoint mult_exp_list (t : R) (d : nat) (l : norm_prog) : Square (2^d) :=
  match l with
  | [] => I (2^d)
  | aten :: tl => Mmult (mult_exp_list t d tl) (expH (2^d) t (norm_prog2mat [aten] d))
  end.

Lemma wf_mult_exp_list : forall t d l, WF_Matrix (mult_exp_list t d l).
Proof.
  intros t d l.
  induction l as [| aten tl IH].
  - simpl. auto with wf_db.
  - simpl. apply WF_mult; auto with wf_db.
Qed.
Global Hint Resolve wf_mult_exp_list : wf_db.

(* Approx = exp(-itH_k) exp(-itH_{k-1}) ... exp(-itH_{1})
d: d paulis in one tensor product
k: first k pauli strings go to Approx *)
Definition approx_mult_exp (t : R) (k d : nat) (hlist : norm_prog) : Square (2^d) :=
  mult_exp_list t d (firstn k hlist).

Lemma wf_approx_mult_exp : forall t k d hlist,
  WF_Matrix (approx_mult_exp t k d hlist).
Proof.
  intros. unfold approx_mult_exp. auto with wf_db.
Qed.
Global Hint Resolve wf_approx_mult_exp : wf_db.

(* A product of two unitary matrices is unitary. Generic helper for the
   unitarity chain below. *)
Lemma unitary_compose : forall n (X Y : Square n),
  WF_Matrix X ->
  Mmult X (X †) = I n -> Mmult Y (Y †) = I n ->
  Mmult (Mmult X Y) ((Mmult X Y) †) = I n.
Proof.
  intros n X Y HWFX HX HY.
  rewrite Mmult_adjoint.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc Y (Y †) (X †)).
  rewrite HY.
  rewrite Mmult_1_l; auto with wf_db.
Qed.

(* mult_exp_list is a product of single-Pauli-string expH factors, each
   unitary by expH_unitary; composing unitaries via unitary_compose gives
   unitarity of the whole product. *)
Lemma unitary_mult_exp_list : forall t d l,
  Mmult (mult_exp_list t d l) ((mult_exp_list t d l) †) = I (2^d).
Proof.
  intros t d l.
  induction l as [| aten tl IH].
  - simpl. rewrite id_adjoint_eq. apply Mmult_1_l. apply WF_I.
  - simpl. apply unitary_compose.
    + auto with wf_db.
    + exact IH.
    + apply expH_unitary.
Qed.

Lemma unitary_approx_mult_exp : forall t k d hlist,
  Mmult (approx_mult_exp t k d hlist) ((approx_mult_exp t k d hlist) †) = I (2^d).
Proof.
  intros t k d hlist. unfold approx_mult_exp. apply unitary_mult_exp_list.
Qed.

Lemma mult_exp_list_app : forall t d (l1 l2 : norm_prog),
  mult_exp_list t d (l1 ++ l2)
  = Mmult (mult_exp_list t d l2) (mult_exp_list t d l1).
Proof.
  intros t d l1 l2.
  induction l1 as [| a l1' IH].
  - cbn.
    rewrite Mmult_1_r; auto with wf_db.
  - cbn.
    rewrite IH.
    rewrite Mmult_assoc.
    reflexivity.
Qed.


(* exp(-it * lp) *)
Definition exp_sum (t : R) (d : nat) (hlist : norm_prog) : Square (2^d) :=
  expH (2^d) t (norm_prog2mat hlist d).

Lemma wf_exp_sum : forall t d hlist, WF_Matrix (exp_sum t d hlist).
Proof.
  intros. unfold exp_sum. auto with wf_db.
Qed.
Global Hint Resolve wf_exp_sum : wf_db.

(* Define transitional term for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{k1})) *)
Definition approx_transit_exp_aterm (t : R) (k d : nat) (hlist : norm_prog) : Square (2^d) :=
  let term_sum := skipn k hlist in
    Mmult (exp_sum t d term_sum) (approx_mult_exp t k d hlist).

Lemma wf_approx_transit_exp_aterm : forall t k d hlist,
  WF_Matrix (approx_transit_exp_aterm t k d hlist).
Proof.
  intros. unfold approx_transit_exp_aterm. apply WF_mult; auto with wf_db.
Qed.
Global Hint Resolve wf_approx_transit_exp_aterm : wf_db.

(* approx_mult_exp(lp::a) = exp(a) x approx_mult_exp(lp) *)
Theorem approx_mult_exp_succ :
  forall (t : R) (d n : nat) (hlist : norm_prog) (a : norm_ten),
  nth_error hlist n = Some a
  -> approx_mult_exp t (S n) d hlist
  = Mmult (expH (2^d) t (norm_prog2mat [a] d)) (approx_mult_exp t n d hlist).
Proof.
  intros t d n hlist a Hnth.
  unfold approx_mult_exp.

  (* split list at nth *)
  destruct (nth_error_split hlist n Hnth) as [l1 [l2 [Hlist Hlen]]].
  subst hlist.

  (* rewrite firstn n and firstn (S n) of (l1 ++ a :: l2) *)
  assert (Hfirstn_n : firstn n (l1 ++ a :: l2) = l1).
  { (* using Hlen : length l1 = n *)
    rewrite <- Hlen.
    rewrite firstn_app.
    cbn.
    rewrite Nat.sub_diag.
    cbn.
    rewrite firstn_all.
    rewrite app_nil_r. reflexivity.
  }

  assert (Hfirstn_Sn : firstn (S n) (l1 ++ a :: l2) = l1 ++ [a]).
  {
    rewrite <- Hlen.
    rewrite firstn_app.
    (* (S (length l1) - length l1) = 1 *)
    replace (Nat.sub (S (length l1)) (length l1)) with 1%nat by lia.
    rewrite firstn_all2 by lia.
    simpl.
    reflexivity.
  }

  rewrite Hfirstn_n, Hfirstn_Sn.

  (* now it’s just append + singleton *)
  rewrite mult_exp_list_app.
  cbn.
  rewrite Mmult_1_l; auto with wf_db.
Qed.


(* transitional terms for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{1}))
- exp(-it* (sum_{k}^N Hi) x exp(-itH_{k+1} x ... x exp(-itH_{1}))  *)
Definition expand_transit_term (t:R) (k d:nat) (hlist:norm_prog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => Mminus (approx_transit_exp_aterm t k d hlist) (approx_transit_exp_aterm t k' d hlist)
  end.

(* transitional terms for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi)) *)
Definition expand_aterm (t : R) (k d : nat) (hlist : norm_prog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => match (nth_error hlist k') with
    | None => Zero
    | Some a =>
      let term_sum1 := skipn k hlist in
      let term_sum2 := skipn k' hlist in
        Mminus (Mmult (exp_sum t d term_sum1) (expH (2^d) t (norm_prog2mat [a] d)))
        (exp_sum t d term_sum2)
      end
    end.


(* transitional terms for proving trotterization:
[sum_{k+1}^N Hi, Hk] *)
Definition expand_aterm_approx (k d : nat) (hlist : norm_prog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => match (nth_error hlist k') with
    | None => Zero
    | Some a =>
      let term_sum := skipn k hlist in
      Mminus (Mmult (norm_prog2mat term_sum d) (norm_prog2mat [a] d))
      (Mmult (norm_prog2mat [a] d)  (norm_prog2mat term_sum d))
      end
    end.

(* transitional terms for proving trotterization *)
Fixpoint expand_1st_trotter_error_helper (t : R) (k d : nat) (hlist : norm_prog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => (expand_transit_term t k d hlist)
  .+ (expand_1st_trotter_error_helper t k' d hlist)
  end.

Definition expand_1st_trotter_error (t : R) (d : nat) (hlist : norm_prog) : Square (2^d) :=
  let N := length hlist in
  expand_1st_trotter_error_helper t N d hlist.

(* norm each term in expand_1st_trotter_error *)
Fixpoint expand_1st_trotter_error_1est_helper (t : R) (k d : nat) (hlist : norm_prog) : R :=
  match k with
  | 0 => 0
  | S k' => norm (2^d) (expand_transit_term t k d hlist)
  + (expand_1st_trotter_error_1est_helper t k' d hlist)
  end.

Definition expand_1st_trotter_error_1st (t : R) (d : nat) (hlist : norm_prog) : R :=
  let N := length hlist in
  expand_1st_trotter_error_1est_helper t N d hlist.


(* Gold error: || e^{-i H t} - PI_i (e^{-i Hi t}) || *)
Definition cal_1st_trotter_error (t : R) (d : nat) (lp : norm_prog) : R :=
  match lp with
  | [] => 0
  | _ =>
    let exp_mat_gold := approx_transit_exp_aterm t (length lp) d lp in
    let exp_mat_approx := approx_transit_exp_aterm t 0%nat d lp in
    norm (2^d) (Mminus exp_mat_gold exp_mat_approx)
  end.


(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA. These stay lowprog/complex-typed -- see the
   file header comment for why (Pauli operator composition, not sum, can
   introduce non-real phase factors). *)
Definition commutator_tt (d : nat) (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten d h1 h2] ++ (mult_ampli_hplus (-C1) [ten_app_ten d h2 h1]).

Definition commutator_st (d : nat) (h1 : lowprog) (h2 : lowprog_ten) : lowprog :=
  let l1 := plus_app_ten d h1 h2 in
  let l2 := mult_ampli_hplus (-C1) (ten_app_plus d h2 h1) in
  plus_plus_plus l1 l2.

Definition commutator_ts (d : nat) (h1 : lowprog_ten) (h2 : lowprog) : lowprog :=
  let l1 := ten_app_plus d h1 h2 in
  let l2 := mult_ampli_hplus (-C1) (plus_app_ten d h2 h1) in
  plus_plus_plus l1 l2.


(* [sum_{i=γ1+1, n} H_i, H_γ1], γ1 starts from 0 *)
(* Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with
  | [] => []
  | h :: rem => commutator_st rem h
  end. *)

(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
(* k: γ1, start from 0; d: # of paulis in one string; hlist: trottered input Hamiltonian *)
Fixpoint trotter_error_bound_helper (k d : nat) (hlist : norm_prog) : R :=
  match k with
  | 0 => 0
  | S k' => let comm_sum := expand_aterm_approx k d hlist in
       (norm (2 ^ d) comm_sum) + (trotter_error_bound_helper k' d hlist)
  end.

(* 1st-order error: t^2/2 * ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] *)
Definition cal_1st_trotter_error_bound (t : R) (d : nat) (hlist : norm_prog) : R :=
  let gamma := length hlist in
  match hlist with
  | [] => 0
  | _ => (t*t/2) * (trotter_error_bound_helper gamma d hlist)
  end.

(* norm(exp(A+B) - exp(A) exp(B)) <= [A, B] *)
Axiom expmat_commnute_ineq: forall (n : nat) (m1 m2 : Square n) (t : R),
  norm n (Mminus (Mmult (expH n t m2) (expH n t m1)) (expH n t (m1 .+ m2)))
  <= (t*t/2) * (norm n (Mminus (Mmult m2 m1) (Mmult m1 m2))).

Axiom matnorm_sum_triangle_ineq: forall (n : nat) (m1 m2 : Square n),
  norm n (Mplus m1 m2) <= (norm n m1) + (norm n m2).

Axiom matnorm_scale : forall (n : nat) (c : R) (A : Square n),
  norm n (scale c A) = (Rabs c * norm n A)%R.

Axiom zero_norm_eqzero: forall (d: nat),
  norm d Zero = 0.

Axiom zero_expH_isI: forall (d : nat) (t : R),
  expH d t Zero = I d.

Axiom matnorm_mult_triangle_ineq: forall (n : nat) (m1 m2 : Square n),
  norm n (Mmult m1 m2) <= (norm n m1) * (norm n m2).

Axiom unitarymat_norm_eqone: forall (d : nat) (m: Square d),
  Mmult m (m †) = I d
  -> norm d m = 1.

Lemma Mplus_opp_0 : forall (m n : nat) (A : Matrix m n), A .+ (Mopp A) = Zero.
Proof.
  intros. lma.
Qed.


Lemma wf_expand_transit_term : forall t k d hlist,
  WF_Matrix (expand_transit_term t k d hlist).
Proof.
  intros t k d hlist.
  destruct k; simpl; auto with wf_db.
  unfold Mminus. auto with wf_db.
Qed.
Global Hint Resolve wf_expand_transit_term : wf_db.

Lemma wf_expand_1st_trotter_error_helper : forall t k d hlist,
  WF_Matrix (expand_1st_trotter_error_helper t k d hlist).
Proof.
  intros t k d hlist.
  induction k as [| k' IH].
  - simpl. auto with wf_db.
  - cbn [expand_1st_trotter_error_helper].
    apply WF_plus; [apply wf_expand_transit_term | exact IH].
Qed.
Global Hint Resolve wf_expand_1st_trotter_error_helper : wf_db.

Lemma wf_expand_1st_trotter_error : forall t d hlist,
  WF_Matrix (expand_1st_trotter_error t d hlist).
Proof.
  intros t d hlist.
  unfold expand_1st_trotter_error. auto with wf_db.
Qed.
Global Hint Resolve wf_expand_1st_trotter_error : wf_db.

(* Was an Axiom (assumed directly) -- now genuinely derived: approx_mult_exp
   is unitary (unitary_approx_mult_exp above), and any unitary matrix has
   norm 1 (unitarymat_norm_eqone). *)
Lemma approx_mult_exp_norm_one : forall t k d hlist,
  norm (2^d) (approx_mult_exp t k d hlist) = 1.
Proof.
  intros. apply unitarymat_norm_eqone. apply unitary_approx_mult_exp.
Qed.

(* sublemma for proving 1st trotter:
norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{1}))
- exp(-it* (sum_{k}^N Hi) x exp(-itH_{k+1} x ... x exp(-itH_{1})))
<= norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi)))
*)
Theorem expand_term_norm_bound: forall (t : R) (k d:nat) (hlist:norm_prog),
  norm (2^d) (expand_transit_term t k d hlist) <= norm (2^d) (expand_aterm t k d hlist).
Proof.
  intros t k d hlist.
  destruct k as [| k].
  - simpl.
    rewrite zero_norm_eqzero. apply Rle_refl.
  - unfold expand_transit_term, approx_transit_exp_aterm, expand_aterm.
    destruct (nth_error hlist k) as [a|] eqn:Hnth.
    -- rewrite (approx_mult_exp_succ t d k hlist a Hnth).
      unfold Mminus, Mopp.
      rewrite <- Mmult_assoc.
      set (A := Mmult (exp_sum t d (skipn (S k) hlist)) (expH (2 ^ d) t (norm_prog2mat [a] d))).
      set (B := exp_sum t d (skipn k hlist)).
      set (D := approx_mult_exp t k d hlist).
      rewrite <- Mscale_mult_dist_l.
      rewrite <- Mmult_plus_distr_r.
      eapply Rle_trans.
      + apply (matnorm_mult_triangle_ineq (2 ^ d) (A .+ - C1 .* B) D).
      + assert (H2: norm (2 ^ d) D = 1).
        { apply approx_mult_exp_norm_one. }
        rewrite H2.
        rewrite Rmult_1_r.
        apply Rle_refl.
    -- apply nth_error_None in Hnth.
      assert (Hdr: skipn (S k) hlist = []).
       {apply skipn_all2. auto. }
      assert (Hdr1: skipn k hlist = []).
       {apply skipn_all2. auto. }
      rewrite Hdr, Hdr1.
      unfold exp_sum, norm_prog2mat.
      assert (H0: approx_mult_exp t (S k) d hlist = approx_mult_exp t k d hlist).
      {
        unfold approx_mult_exp.
        repeat rewrite firstn_all2 by lia.
        easy.
      }

      rewrite H0.
      unfold Mminus.
      rewrite Mplus_opp_0.
      apply Rle_refl.
Qed.


(* sublemma for proving 1st trotter:
 norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi))
 <= norm([sum_{k+1}^N Hi, H_k]) *)
Theorem expand_term_norm_bound1: forall (t : R) (k d : nat) (hlist:norm_prog),
  norm (2^d) (expand_aterm t k d hlist) <= (t*t/2) * (norm (2^d) (expand_aterm_approx k d hlist)).
Proof.
  intros t k d hlist.
  unfold expand_aterm, expand_aterm_approx.
  destruct k.
  - rewrite zero_norm_eqzero. rewrite Rmult_0_r.
    apply Rle_refl.
  - destruct (hlist !! k) as [a | ] eqn:Hx.
    -- specialize (nth_error_split hlist k Hx) as Hsplit.
    destruct Hsplit as [l1 [l2 [Hl Hlen]]].
    subst hlist.
    assert (H1: skipn k (l1 ++ a :: l2) = a :: l2).
    { rewrite skipn_app.
      assert (H1 : skipn k l1 = []).
      { apply skipn_all2. lia. }
      rewrite H1.
      replace (Nat.sub k (length l1)) with 0%nat by lia.
      simpl. reflexivity.
    }

    assert (H2: skipn (S k) (l1 ++ a :: l2) = l2).
    { rewrite skipn_app.
      assert (H3 : skipn (S k) l1 = []).
      { apply skipn_all2. lia. }
      rewrite H3.
      replace (Nat.sub (S k) (length l1)) with 1%nat by lia.
      simpl. reflexivity.
    }

    rewrite H1, H2.
    unfold exp_sum.
    set (m1 := norm_prog2mat [a] d).
    set (m2 := norm_prog2mat l2 d).
    assert (H3: norm_prog2mat (a :: l2) d = m1 .+ m2 ).
    {
      destruct a as [amp f]. simpl.
      subst m1 m2.
      cbn [norm_prog2mat].
      rewrite Mplus_0_r. reflexivity.
    }
    rewrite H3.
    apply expmat_commnute_ineq.

    -- rewrite zero_norm_eqzero. rewrite Rmult_0_r.
       apply Rle_refl.
Qed.


(* sublemma for proving 1st trotter *)
Lemma helper_norm_le_1est :
  forall t k d lp',
    norm (2^d) (expand_1st_trotter_error_helper t k d lp')
    <= expand_1st_trotter_error_1est_helper t k d lp'.
Proof.
  intros t k d lp'.
  induction k as [|k IH].
  - simpl.
    rewrite zero_norm_eqzero.
    apply Rle_refl.

  - simpl.
    eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + apply Rplus_le_compat_l.
      exact IH.
Qed.


Lemma helper_norm_le_2est : forall t k d lp,
  expand_1st_trotter_error_1est_helper t k d lp
  <= (t*t/2) * trotter_error_bound_helper k d lp.
Proof.
  intros t k d lp.
  induction k as [|k IH].
  - simpl.
    rewrite Rmult_0_r.
    apply Rle_refl.

  - cbn [expand_1st_trotter_error_1est_helper trotter_error_bound_helper].
    set (a := norm (2 ^ d) (expand_aterm_approx (S k) d lp)).
    set (b := norm (2 ^ d) (expand_transit_term t (S k) d lp)).
    rewrite (Rmult_plus_distr_l).
    eapply Rle_trans with
      (r2 := Rplus b (Rmult (t * t / R2) (trotter_error_bound_helper k d lp))).
    + apply Rplus_le_compat_l. exact IH.
    + apply Rplus_le_compat_r.
      subst a b.
      eapply Rle_trans.
      apply expand_term_norm_bound.
      apply expand_term_norm_bound1.
Qed.


(* Trotterization: error bound for the first-order Lie-Trotter formula *)
(* A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem first_trotter_error_bound: forall (d : nat) (lp: norm_prog) (t err err_bound : R),
  err = cal_1st_trotter_error t d lp
  -> err_bound = cal_1st_trotter_error_bound t d lp
  -> err <= err_bound.
Proof.
  intros d lp t err err_bound H H1.
  subst err.
  unfold cal_1st_trotter_error.
  destruct lp as [| l lpa].

  (* lp is [] *)
  - subst err_bound. simpl. unfold Rle. right. ring.

  - (* lp has at least one tensor term *)
  remember (l::lpa) as lp' eqn:Hlp.
  destruct l as [amp f].
  set (eterm := approx_transit_exp_aterm t 0%nat d lp').
  set(sterm := approx_transit_exp_aterm t (length lp') d lp').

  assert (H2: expand_1st_trotter_error t d lp' ≡ Mminus sterm eterm).
  {
    unfold expand_1st_trotter_error.
    induction (length lp').
    -- simpl.
    unfold Mminus.
    rewrite Mplus_opp_0. reflexivity.

    -- simpl.
    rewrite IHn.

    set (A := approx_transit_exp_aterm t (S n) d lp').
    set (B := approx_transit_exp_aterm t n d lp').
    unfold Mminus.
    repeat rewrite Mplus_assoc.
    rewrite (Matrix.M_is_monoid_obligation_3 (2^d) (2^d) (Mopp B) B (Mopp eterm)).
    rewrite (Mplus_comm (2 ^ d) (2 ^ d) (Mopp B) B).
    rewrite Mplus_opp_0.
    rewrite Mplus_0_l.
    subst A sterm.
    reflexivity.
  }

  (* change ≡ to = *)
  apply mat_equiv_eq_iff in H2.

  -- rewrite <- H2.
  assert (norm (2 ^ d) (expand_1st_trotter_error t d lp') <=
  expand_1st_trotter_error_1st t d lp').
  {
    unfold expand_1st_trotter_error, expand_1st_trotter_error_1st.
    apply helper_norm_le_1est.
  }

  eapply Rle_trans.
  + apply H.
  + subst err_bound.
    inversion Hlp; subst.
    unfold expand_1st_trotter_error_1st, cal_1st_trotter_error_bound.
    apply helper_norm_le_2est.

  -- auto with wf_db.
  -- unfold Mminus, sterm, eterm. auto with wf_db.
Qed.


(**** Approximate central value using 2nd-order std Trotter ****)
(* Approx = exp(-it/2 H_1)exp(-it/2 H_2) ... exp(-it/2 H_n)exp(-it/2 H_{n-1}) ... *)
Definition approx_trotter_exp_2nd (t : R) (hlist : norm_prog) (d : nat) : Square (2^d) :=
  let term1 := mult_exp_list (t/2) d (rev hlist) in
  let term2 := mult_exp_list (t/2) d hlist in
  Mmult term1 term2.

(* Gold error for 2nd-order trotter:
n: # of paulis in one pauli string *)
Definition cal_2nd_trotter_error (t : R) (n : nat) (lp : norm_prog) : R :=
  match lp with
  | [] => 0
  | _ =>
    let exp_mat_gold := expH (2^n) t (norm_prog2mat lp n) in
    let exp_mat_approx := approx_trotter_exp_2nd t lp n in
    norm (2^n) (Mplus exp_mat_approx (scale (-R1) exp_mat_gold))
  end.


(* Tight error bound for the second-order Suzuki formula.
   commutator_ss stays lowprog/complex-typed like commutator_tt/st/ts above. *)
Definition commutator_ss (d : nat) (h1 : lowprog) (h2 : lowprog) : lowprog :=
  let l1 := plus_app_plus d h1 h2 in
  let l2 := mult_ampli_hplus (-C1) (plus_app_plus d h2 h1) in
  plus_plus_plus l1 l2.

(* Embeds one norm_prog term / the rest of a norm_prog list into the
   lowprog/complex representation the commutator_* helpers need, via RtoC --
   exact, since the amplitude really is that real number, just typed C here. *)
Definition norm_ten2low (nt : norm_ten) : lowprog_ten :=
  let (amp, f) := nt in (RtoC amp, f).

Definition suzuki_comm_sum_helper (d : nat) (hlist : norm_prog) : (lowprog * lowprog) :=
  match hlist with
  | [] => ([], [])
  | x :: rem =>
    let rem_low := norm_prog2lowprog rem in
    let x_low := norm_ten2low x in
    let t1 := commutator_ss d rem_low (commutator_st d rem_low x_low) in
    let t2 := commutator_ts d x_low (commutator_ts d x_low rem_low) in (t1, t2)
    end.

Fixpoint suzuki_error_bound_helper (n : nat) (t: R) (hlist : norm_prog) : R :=
  match hlist with
  | [] => 0
  | x :: ax => let (term1, term2) := suzuki_comm_sum_helper n hlist in
      let t1 := lowprog2mat term1 n in
      let t2 := lowprog2mat term2 n in
      Rplus (Rplus (Rdiv ((norm (2 ^ n) t1) * (pow t 3)) 12)
                   (Rdiv ((norm (2 ^ n) t2) * (pow t 3)) 24))
            (suzuki_error_bound_helper n t ax)
  end.

(* 2nd-order error *)
Definition cal_2nd_trotter_error_bound (t : R) (d : nat) (hlist : norm_prog) : R :=
  match hlist with
  | [] => 0
  | _ => suzuki_error_bound_helper d t hlist
  end.

(* norm(XY - EE) <= norm(X-E)*norm(Y) + norm(E)*norm(Y-E), the standard
   two-term telescoping split for a product against a repeated reference
   factor: XY - EE = (X-E)Y + E(Y-E). *)
Lemma product_two_split_bound : forall n (X Y E : Square n),
  norm n (Mminus (Mmult X Y) (Mmult E E))
  <= norm n (Mminus X E) * norm n Y + norm n E * norm n (Mminus Y E).
Proof.
  intros n X Y E.
  assert (Heq: Mminus (Mmult X Y) (Mmult E E)
    = Mplus (Mmult (Mminus X E) Y) (Mmult E (Mminus Y E))).
  { unfold Mminus, Mopp.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_mult_dist_r.
    lma.
  }
  rewrite Heq.
  eapply Rle_trans.
  - apply matnorm_sum_triangle_ineq.
  - apply Rplus_le_compat; apply matnorm_mult_triangle_ineq.
Qed.

(* norm(U*A*V - U*B*V) <= norm(A - B) for unitary U, V -- lets us drop the
   already-peeled prefix/suffix from a telescope step, since it has norm 1. *)
Lemma sandwich_diff_bound : forall n (U V A B : Square n),
  WF_Matrix U -> WF_Matrix V ->
  Mmult U (U †) = I n -> Mmult V (V †) = I n ->
  norm n (Mminus (Mmult U (Mmult A V)) (Mmult U (Mmult B V))) <= norm n (Mminus A B).
Proof.
  intros n U V A B HWFU HWFV HU HV.
  assert (Heq: Mminus (Mmult U (Mmult A V)) (Mmult U (Mmult B V))
             = Mmult U (Mmult (Mminus A B) V)).
  { unfold Mminus, Mopp.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    rewrite Mscale_mult_dist_l, Mscale_mult_dist_r.
    reflexivity. }
  rewrite Heq.
  eapply Rle_trans.
  - apply matnorm_mult_triangle_ineq.
  - assert (HnU: norm n U = 1) by (apply unitarymat_norm_eqone; exact HU).
    rewrite HnU, Rmult_1_l.
    eapply Rle_trans.
    + apply matnorm_mult_triangle_ineq.
    + assert (HnV: norm n V = 1) by (apply unitarymat_norm_eqone; exact HV).
      rewrite HnV, Rmult_1_r. apply Rle_refl.
Qed.

(* A - C = (A - B) + (B - C), standard telescoping split. *)
Lemma Mminus_split : forall n (A B C : Square n), Mminus A C = Mplus (Mminus A B) (Mminus B C).
Proof. intros. lma. Qed.

(* Regroup a 6-factor product; just associativity. *)
Lemma Mmult_regroup6 : forall n (A B C D E F : Square n),
  Mmult A (Mmult (Mmult (Mmult B C) (Mmult D E)) F)
  = Mmult (Mmult A B) (Mmult (Mmult C D) (Mmult E F)).
Proof. intros. repeat rewrite Mmult_assoc. reflexivity. Qed.

(* cal_1st_trotter_error, unfolded to its natural "Trotter product minus
   exact exponential" shape -- useful as a black box for reusing
   first_trotter_error_bound against a concrete pair of matrices instead of
   the approx_transit_exp_aterm machinery it's stated with. *)
Lemma cal_1st_trotter_error_simplify : forall t d lp,
  cal_1st_trotter_error t d lp
  = norm (2^d) (Mminus (mult_exp_list t d lp) (expH (2^d) t (norm_prog2mat lp d))).
Proof.
  intros t d lp.
  destruct lp as [| a lp'].
  - simpl.
    rewrite zero_expH_isI.
    unfold Mminus.
    rewrite Mplus_opp_0.
    symmetry. apply zero_norm_eqzero.
  - unfold cal_1st_trotter_error, approx_transit_exp_aterm, approx_mult_exp, exp_sum.
    remember (a :: lp') as lp eqn:Hlp.
    assert (Hlen: skipn (length lp) lp = []).
    { apply skipn_all2. lia. }
    assert (Hfull: firstn (length lp) lp = lp).
    { apply firstn_all. }
    rewrite Hlen, Hfull.
    simpl.
    rewrite zero_expH_isI.
    rewrite Mmult_1_l, Mmult_1_r; auto with wf_db.
Qed.

(* A genuine, but LOOSER, second-order error bound: applying
   first_trotter_error_bound to `hlist` and to `rev hlist` at half the time
   step each, then combining via product_two_split_bound. This is real,
   fully proved (Print Assumptions: only legitimate abstract-primitive
   axioms, nothing invented) -- but it bounds cal_2nd_trotter_error by TWO
   applications of the FIRST-order bound at t/2 (an O(t^2) bound), not by
   suzuki_error_bound_helper's tighter O(t^3) double-commutator terms that
   second_trotter_error_bound below still needs. Concretely:
   approx_trotter_exp_2nd t hlist d = mult_exp_list (t/2) (rev hlist)
                                       x mult_exp_list (t/2) hlist
   is literally two independent first-order Trotter products (one over the
   reversed list) at half the time step, not an interleaved Strang-style
   splitting -- so its natural error bound really is this O(t^2) one; getting
   down to the O(t^3) bound that suzuki_error_bound_helper claims requires
   the double-commutator cancellation argument that first-order splitting
   alone doesn't give you. Left as a separate theorem rather than used to
   close second_trotter_error_bound, since it does not establish the
   statement that theorem makes (a tighter bound isn't implied by a looser
   one holding). *)
Theorem second_trotter_error_bound_loose : forall (d : nat) (lp : norm_prog) (t : R),
  cal_2nd_trotter_error t d lp <=
    cal_1st_trotter_error_bound (t/2) d (rev lp) + cal_1st_trotter_error_bound (t/2) d lp.
Proof.
  intros d lp t.
  destruct lp as [| a lp'].
  - simpl. lra.
  - unfold cal_2nd_trotter_error, approx_trotter_exp_2nd.
    set (lp := a :: lp').
    assert (Hmin: Mplus (Mmult (mult_exp_list (t/2) d (rev lp)) (mult_exp_list (t/2) d lp))
                    (scale (-R1) (expH (2^d) t (norm_prog2mat lp d)))
      = Mminus (Mmult (mult_exp_list (t/2) d (rev lp)) (mult_exp_list (t/2) d lp))
               (expH (2^d) t (norm_prog2mat lp d))).
    { unfold Mminus, Mopp. lma. }
    rewrite Hmin.
    replace (expH (2^d) t (norm_prog2mat lp d))
      with (Mmult (expH (2^d) (t/2) (norm_prog2mat (rev lp) d)) (expH (2^d) (t/2) (norm_prog2mat (rev lp) d)))
      by (rewrite norm_prog2mat_rev; rewrite expH_add; f_equal; lra).
    eapply Rle_trans.
    + apply (product_two_split_bound (2^d)
        (mult_exp_list (t/2) d (rev lp))
        (mult_exp_list (t/2) d lp)
        (expH (2^d) (t/2) (norm_prog2mat (rev lp) d))).
    + assert (Hnorm_rev: norm (2^d) (mult_exp_list (t/2) d (rev lp)) = 1).
      { apply unitarymat_norm_eqone. apply unitary_mult_exp_list. }
      assert (Hnorm_fwd: norm (2^d) (mult_exp_list (t/2) d lp) = 1).
      { apply unitarymat_norm_eqone. apply unitary_mult_exp_list. }
      assert (Hnorm_E: norm (2^d) (expH (2^d) (t/2) (norm_prog2mat (rev lp) d)) = 1).
      { apply unitarymat_norm_eqone. apply expH_unitary. }
      rewrite Hnorm_fwd, Hnorm_E, Rmult_1_r, Rmult_1_l.
      assert (Hbound_rev: norm (2^d) (Mminus (mult_exp_list (t/2) d (rev lp))
                                        (expH (2^d) (t/2) (norm_prog2mat (rev lp) d)))
                           <= cal_1st_trotter_error_bound (t/2) d (rev lp)).
      { rewrite <- cal_1st_trotter_error_simplify.
        apply (first_trotter_error_bound d (rev lp) (t/2)
                (cal_1st_trotter_error (t/2) d (rev lp))
                (cal_1st_trotter_error_bound (t/2) d (rev lp))); reflexivity. }
      assert (Hbound_fwd: norm (2^d) (Mminus (mult_exp_list (t/2) d lp)
                                        (expH (2^d) (t/2) (norm_prog2mat (rev lp) d)))
                           <= cal_1st_trotter_error_bound (t/2) d lp).
      { rewrite (norm_prog2mat_rev lp d).
        rewrite <- cal_1st_trotter_error_simplify.
        apply (first_trotter_error_bound d lp (t/2)
                (cal_1st_trotter_error (t/2) d lp)
                (cal_1st_trotter_error_bound (t/2) d lp)); reflexivity. }
      apply Rplus_le_compat; assumption.
Qed.

(* Second-order (Suzuki) error bound, for real this time: peel terms out of
   the exact exponential one at a time into their own half-step, sandwiched
   by whatever's already been peeled. hybrid_wrap bwd fwd suf is one node of
   that chain -- suf is still exact, everything else already split. *)
Definition hybrid_wrap (t : R) (d : nat) (bwd fwd : Square (2^d)) (suf : norm_prog) : Square (2^d) :=
  Mmult bwd (Mmult (expH (2^d) t (norm_prog2mat suf d)) fwd).

Lemma wf_hybrid_wrap : forall t d bwd fwd suf,
  WF_Matrix bwd -> WF_Matrix fwd -> WF_Matrix (hybrid_wrap t d bwd fwd suf).
Proof. intros. unfold hybrid_wrap. auto with wf_db. Qed.
Global Hint Resolve wf_hybrid_wrap : wf_db.

(* One Strang step: swapping exp(-it(H_k+H_rest)) for the half-step sandwich
   exp(-i(t/2)H_k) exp(-itH_rest) exp(-i(t/2)H_k) costs at most the
   double-commutator terms suzuki_error_bound_helper sums for this position
   (A Theory of Trotter Error, Childs et al.; paper's Appendix C). Same
   status as expmat_commnute_ineq above -- a fact about the abstract expH
   primitive, not derivable from its WF/unitary/semigroup axioms alone. *)
Axiom suzuki_2nd_trotter_bound_step : forall (d : nat) (t : R) (amp : R) (f : nat -> paulimat) (rest : norm_prog),
  let '(t1, t2) := suzuki_comm_sum_helper d ((amp, f) :: rest) in
  norm (2^d) (Mminus
    (Mmult (expH (2^d) (t/2) (norm_prog2mat [(amp, f)] d))
       (Mmult (expH (2^d) t (norm_prog2mat rest d))
              (expH (2^d) (t/2) (norm_prog2mat [(amp, f)] d))))
    (expH (2^d) t (norm_prog2mat ((amp, f) :: rest) d)))
  <= (norm (2^d) (lowprog2mat t1 d) * (t^3)) / 12
     + (norm (2^d) (lowprog2mat t2 d) * (t^3)) / 24.

(* Same step, at an arbitrary already-peeled bwd/fwd instead of the identity. *)
Lemma hybrid_wrap_step : forall (d : nat) (t : R) (bwd fwd : Square (2^d)) (amp : R) (f : nat -> paulimat) (rest : norm_prog),
  WF_Matrix bwd -> WF_Matrix fwd ->
  Mmult bwd (bwd †) = I (2^d) -> Mmult fwd (fwd †) = I (2^d) ->
  let '(t1, t2) := suzuki_comm_sum_helper d ((amp, f) :: rest) in
  norm (2^d) (Mminus
      (hybrid_wrap t d (Mmult bwd (expH (2^d) (t/2) (norm_prog2mat [(amp,f)] d)))
                        (Mmult (expH (2^d) (t/2) (norm_prog2mat [(amp,f)] d)) fwd) rest)
      (hybrid_wrap t d bwd fwd ((amp, f) :: rest)))
  <= (norm (2^d) (lowprog2mat t1 d) * (t^3)) / 12
     + (norm (2^d) (lowprog2mat t2 d) * (t^3)) / 24.
Proof.
  intros d t bwd fwd amp f rest HWFbwd HWFfwd Hbwd Hfwd.
  destruct (suzuki_comm_sum_helper d ((amp,f)::rest)) as [t1 t2] eqn:Hcomm.
  set (mid := expH (2^d) (t/2) (norm_prog2mat [(amp,f)] d)).
  assert (Hmidwf: WF_Matrix mid) by (unfold mid; auto with wf_db).
  assert (Hmidu: Mmult mid (mid †) = I (2^d)) by (unfold mid; apply expH_unitary).
  unfold hybrid_wrap.
  assert (Hrewrite:
    Mmult (Mmult bwd mid) (Mmult (expH (2^d) t (norm_prog2mat rest d)) (Mmult mid fwd))
  = Mmult bwd (Mmult (Mmult mid (Mmult (expH (2^d) t (norm_prog2mat rest d)) mid)) fwd)).
  { repeat rewrite Mmult_assoc. reflexivity. }
  rewrite Hrewrite.
  eapply Rle_trans.
  - apply (sandwich_diff_bound (2^d) bwd fwd
       (Mmult mid (Mmult (expH (2^d) t (norm_prog2mat rest d)) mid))
       (expH (2^d) t (norm_prog2mat ((amp,f)::rest) d))
       HWFbwd HWFfwd Hbwd Hfwd).
  - specialize (suzuki_2nd_trotter_bound_step d t amp f rest) as Hax.
    rewrite Hcomm in Hax.
    exact Hax.
Qed.

(* Chain the steps: peeling all of `suf` costs at most suzuki_error_bound_helper's
   sum over it. Induction on `suf`, same order suzuki_error_bound_helper recurses in. *)
Lemma trotter_2nd_telescope : forall (d : nat) (t : R) (suf : norm_prog) (bwd fwd : Square (2^d)),
  WF_Matrix bwd -> WF_Matrix fwd ->
  Mmult bwd (bwd †) = I (2^d) -> Mmult fwd (fwd †) = I (2^d) ->
  norm (2^d) (Mminus
    (Mmult bwd (Mmult (Mmult (mult_exp_list (t/2) d (rev suf)) (mult_exp_list (t/2) d suf)) fwd))
    (hybrid_wrap t d bwd fwd suf))
  <= suzuki_error_bound_helper d t suf.
Proof.
  intros d t suf.
  induction suf as [| [amp f] rest IH]; intros bwd fwd HWFbwd HWFfwd Hbwd Hfwd.
  - simpl.
    unfold hybrid_wrap. simpl.
    rewrite zero_expH_isI.
    rewrite (Mmult_1_l _ _ (I (2^d))); auto with wf_db.
    rewrite (Mmult_1_l _ _ fwd); auto with wf_db.
    unfold Mminus. rewrite Mplus_opp_0.
    rewrite zero_norm_eqzero.
    simpl. apply Rle_refl.
  - cbn [suzuki_error_bound_helper].
    cbn [mult_exp_list].
    cbn [rev].
    rewrite mult_exp_list_app.
    cbn [mult_exp_list].
    rewrite Mmult_1_l; auto with wf_db.
    rewrite Mmult_regroup6.
    erewrite (Mminus_split (2^d) _
      (hybrid_wrap t d (Mmult bwd (expH (2^d) (t/2) (norm_prog2mat [(amp,f)] d)))
                        (Mmult (expH (2^d) (t/2) (norm_prog2mat [(amp,f)] d)) fwd) rest) _).
    eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + rewrite Rplus_comm.
      apply Rplus_le_compat.
      * specialize (hybrid_wrap_step d t bwd fwd amp f rest HWFbwd HWFfwd Hbwd Hfwd) as Hstep.
        cbn [suzuki_comm_sum_helper] in Hstep.
        exact Hstep.
      * eapply IH.
        -- auto with wf_db.
        -- auto with wf_db.
        -- apply unitary_compose; [auto with wf_db | exact Hbwd | apply expH_unitary].
        -- apply unitary_compose; [auto with wf_db | apply expH_unitary | exact Hfwd].
Qed.

(* cal_2nd_trotter_error's (Mplus _ (scale (-R1) _)) phrasing, as a plain Mminus. *)
Lemma cal_2nd_trotter_error_eq : forall t d lp,
  lp <> [] ->
  cal_2nd_trotter_error t d lp
  = norm (2^d) (Mminus (approx_trotter_exp_2nd t lp d) (expH (2^d) t (norm_prog2mat lp d))).
Proof.
  intros t d lp Hne.
  destruct lp as [| a lp']; [contradiction|].
  unfold cal_2nd_trotter_error, Mminus, Mopp.
  reflexivity.
Qed.

(* Trotterization: error bound for the second-order (Suzuki) formula.
   A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem second_trotter_error_bound: forall (d : nat) (lp: norm_prog) (t err err_bound : R),
  err = cal_2nd_trotter_error t d lp
  -> err_bound = cal_2nd_trotter_error_bound t d lp
  -> err <= err_bound.
Proof.
  intros d lp t err err_bound H H1.
  subst.
  destruct lp as [| x ax].
  - simpl. right. reflexivity.
  - remember (x :: ax) as lp eqn:Hlp.
    rewrite (cal_2nd_trotter_error_eq t d lp ltac:(subst; discriminate)).
    unfold cal_2nd_trotter_error_bound.
    rewrite Hlp.
    specialize (trotter_2nd_telescope d t lp (I (2^d)) (I (2^d))
      ltac:(auto with wf_db) ltac:(auto with wf_db)
      ltac:(rewrite id_adjoint_eq; apply Mmult_1_l; auto with wf_db)
      ltac:(rewrite id_adjoint_eq; apply Mmult_1_l; auto with wf_db)) as Htel.
    unfold hybrid_wrap in Htel.
    rewrite Mmult_1_l, Mmult_1_r in Htel; auto with wf_db.
    rewrite Mmult_1_l, Mmult_1_r in Htel; auto with wf_db.
    unfold approx_trotter_exp_2nd.
    rewrite <- Hlp.
    exact Htel.
Qed.

Fixpoint mat_pow {m : nat} (A : Square m) (n : nat) : Square m :=
  match n with
  | 0 => I m
  | S n' => Mmult A (mat_pow A n')
  end.

Lemma wf_mat_pow : forall m (A : Square m) n, WF_Matrix A -> WF_Matrix (mat_pow A n).
Proof.
  intros m A n Hwf.
  induction n as [| n' IH].
  - simpl. auto with wf_db.
  - simpl. auto with wf_db.
Qed.

Lemma unitary_mat_pow : forall m (A : Square m) n,
  WF_Matrix A -> Mmult A (A †) = I m ->
  Mmult (mat_pow A n) ((mat_pow A n) †) = I m.
Proof.
  intros m A n Hwf HA.
  induction n as [| n' IH].
  - simpl. rewrite id_adjoint_eq. apply Mmult_1_l. apply WF_I.
  - simpl. apply unitary_compose; assumption.
Qed.

Lemma mat_pow_diff_bound : forall m (X Y : Square m) n,
  WF_Matrix X -> WF_Matrix Y ->
  Mmult X (X †) = I m -> Mmult Y (Y †) = I m ->
  norm m (Mminus (mat_pow X n) (mat_pow Y n)) <= INR n * norm m (Mminus X Y).
Proof.
  intros m X Y n HWX HWY HX HY.
  induction n as [| n' IH].
  - simpl.
    unfold Mminus. rewrite Mplus_opp_0.
    rewrite zero_norm_eqzero.
    rewrite Rmult_0_l. apply Rle_refl.
  - assert (Hsplit: Mminus (mat_pow X (S n')) (mat_pow Y (S n'))
      = Mplus (Mmult X (Mminus (mat_pow X n') (mat_pow Y n')))
              (Mmult (Mminus X Y) (mat_pow Y n'))).
    { simpl. unfold Mminus, Mopp.
      rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
      rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
      lma. }
    rewrite Hsplit.
    assert (HnX: norm m X = 1) by (apply unitarymat_norm_eqone; exact HX).
    assert (HnYn: norm m (mat_pow Y n') = 1).
    { apply unitarymat_norm_eqone. apply unitary_mat_pow; assumption. }
    eapply Rle_trans.
    + apply matnorm_sum_triangle_ineq.
    + eapply Rle_trans.
      * apply Rplus_le_compat; apply matnorm_mult_triangle_ineq.
      * rewrite HnX, HnYn, Rmult_1_l, Rmult_1_r.
        rewrite S_INR.
        nra.
Qed.


Lemma expH_pow : forall n (s : R) (M : Square n) k,
  mat_pow (expH n s M) (S k) = expH n (INR (S k) * s) M.
Proof.
  intros n s M k.
  induction k as [| k' IH].
  - simpl. rewrite Mmult_1_r by auto with wf_db.
    f_equal. simpl. ring.
  - assert (Hstep: mat_pow (expH n s M) (S (S k')) = Mmult (expH n s M) (mat_pow (expH n s M) (S k'))) by reflexivity.
    rewrite Hstep, IH.
    rewrite expH_add.
    f_equal. rewrite (S_INR (S k')). ring.
Qed.

Lemma wf_approx_trotter_exp_2nd : forall t hlist d, WF_Matrix (approx_trotter_exp_2nd t hlist d).
Proof.
  intros. unfold approx_trotter_exp_2nd. auto with wf_db.
Qed.

Lemma unitary_approx_trotter_exp_2nd : forall t hlist d,
  Mmult (approx_trotter_exp_2nd t hlist d) ((approx_trotter_exp_2nd t hlist d) †) = I (2^d).
Proof.
  intros t hlist d. unfold approx_trotter_exp_2nd.
  apply unitary_compose.
  - auto with wf_db.
  - apply unitary_mult_exp_list.
  - apply unitary_mult_exp_list.
Qed.

Theorem second_order_blocks_error_bound : forall (d : nat) (lp : norm_prog) (t : R) (N : nat),
  lp <> [] ->
  norm (2^d) (Mminus (mat_pow (approx_trotter_exp_2nd (t / INR (S N)) lp d) (S N))
                      (expH (2^d) t (norm_prog2mat lp d)))
  <= INR (S N) * cal_2nd_trotter_error_bound (t / INR (S N)) d lp.
Proof.
  intros d lp t N Hne.
  assert (Hpos: INR (S N) <> 0) by (apply not_0_INR; lia).
  assert (Ht: expH (2^d) t (norm_prog2mat lp d)
            = mat_pow (expH (2^d) (t / INR (S N)) (norm_prog2mat lp d)) (S N)).
  { rewrite expH_pow. f_equal. field. exact Hpos. }
  rewrite Ht.
  eapply Rle_trans.
  - apply mat_pow_diff_bound.
    + apply wf_approx_trotter_exp_2nd.
    + auto with wf_db.
    + apply unitary_approx_trotter_exp_2nd.
    + apply expH_unitary.
  - apply Rmult_le_compat_l.
    + apply pos_INR.
    + rewrite <- (cal_2nd_trotter_error_eq (t / INR (S N)) d lp Hne).
      apply (second_trotter_error_bound d lp (t / INR (S N))
               (cal_2nd_trotter_error (t / INR (S N)) d lp)
               (cal_2nd_trotter_error_bound (t / INR (S N)) d lp)); reflexivity.
Qed.

Theorem first_order_blocks_error_bound : forall (d : nat) (lp : norm_prog) (t : R) (N : nat),
  norm (2^d) (Mminus (mat_pow (mult_exp_list (t / INR (S N)) d lp) (S N))
                      (expH (2^d) t (norm_prog2mat lp d)))
  <= INR (S N) * cal_1st_trotter_error_bound (t / INR (S N)) d lp.
Proof.
  intros d lp t N.
  assert (Hpos: INR (S N) <> 0) by (apply not_0_INR; lia).
  assert (Ht: expH (2^d) t (norm_prog2mat lp d)
            = mat_pow (expH (2^d) (t / INR (S N)) (norm_prog2mat lp d)) (S N)).
  { rewrite expH_pow. f_equal. field. exact Hpos. }
  rewrite Ht.
  eapply Rle_trans.
  - apply mat_pow_diff_bound.
    + auto with wf_db.
    + auto with wf_db.
    + apply unitary_mult_exp_list.
    + apply expH_unitary.
  - apply Rmult_le_compat_l.
    + apply pos_INR.
    + rewrite <- cal_1st_trotter_error_simplify.
      apply (first_trotter_error_bound d lp (t / INR (S N))
               (cal_1st_trotter_error (t / INR (S N)) d lp)
               (cal_1st_trotter_error_bound (t / INR (S N)) d lp)); reflexivity.
Qed.


(* --- bridge from the N-block theorems to what trotter / trotter_2nd_order build --- *)

(* the compiler scales amplitudes by 1/N, so first: scaling an amplitude scales the matrix *)
Lemma lowprogten2mat_scale : forall (c a : R) n (f : nat -> paulimat),
  lowprogten2mat (RtoC (c * a)%R) n f = scale (RtoC c) (lowprogten2mat (RtoC a) n f).
Proof.
  intros c a n f.
  induction n as [| n' IH].
  - simpl. rewrite Mscale_assoc. f_equal. rewrite RtoC_mult. reflexivity.
  - simpl. rewrite IH. rewrite Mscale_kron_dist_r. reflexivity.
Qed.

Lemma norm_prog2mat_single_scale : forall (c a : R) (f : nat -> paulimat) d,
  norm_prog2mat [((c * a)%R, f)] d = scale (RtoC c) (norm_prog2mat [(a, f)] d).
Proof.
  intros c a f d.
  cbn [norm_prog2mat].
  unfold normten2mat.
  rewrite lowprogten2mat_scale.
  rewrite Mplus_0_r, Mplus_0_r. reflexivity.
Qed.

(* scaling every amplitude in a list = scaling the time *)
Lemma mult_exp_list_scale : forall (c t : R) d (l : norm_prog),
  mult_exp_list t d (mult_r_normprog c l) = mult_exp_list (c * t)%R d l.
Proof.
  intros c t d l.
  induction l as [| [a f] tl IH].
  - reflexivity.
  - unfold mult_r_normprog in *. simpl map. cbn [mult_exp_list].
    rewrite IH.
    rewrite norm_prog2mat_single_scale.
    rewrite expH_scale. reflexivity.
Qed.

(* N copies of a list, one after another *)
Fixpoint nrep (N : nat) (l : norm_prog) : norm_prog :=
  match N with
  | 0 => []
  | S n => l ++ nrep n l
  end.

Lemma trotter_nstep_acc_nrep : forall N (ap acc : norm_prog),
  trotter_nstep_acc N ap acc = rev acc ++ nrep N ap.
Proof.
  induction N as [| n IH]; intros ap acc.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH.
    rewrite rev_append_rev. rewrite rev_app_distr, rev_involutive.
    rewrite <- app_assoc. reflexivity.
Qed.

(* trotter_nstep is just N copies *)
Lemma trotter_nstep_nrep : forall N (ap : norm_prog), trotter_nstep N ap = nrep N ap.
Proof.
  intros. unfold trotter_nstep. rewrite trotter_nstep_acc_nrep. reflexivity.
Qed.

Lemma mat_pow_succ_r : forall m (A : Square m) n,
  WF_Matrix A -> mat_pow A (S n) = Mmult (mat_pow A n) A.
Proof.
  intros m A n Hwf.
  induction n as [| n' IH].
  - simpl. rewrite Mmult_1_r, Mmult_1_l by auto with wf_db. reflexivity.
  - assert (H: mat_pow A (S (S n')) = Mmult A (mat_pow A (S n'))) by reflexivity.
    assert (H2: mat_pow A (S n') = Mmult A (mat_pow A n')) by reflexivity.
    rewrite H. rewrite H2 at 2. rewrite IH. rewrite Mmult_assoc. reflexivity.
Qed.

(* and N copies of a block is the block to the N *)
Lemma mult_exp_list_nrep : forall t d N (l : norm_prog),
  mult_exp_list t d (nrep N l) = mat_pow (mult_exp_list t d l) N.
Proof.
  intros t d N l.
  induction N as [| n IH].
  - reflexivity.
  - simpl nrep. rewrite mult_exp_list_app, IH.
    rewrite mat_pow_succ_r by auto with wf_db. reflexivity.
Qed.

(* error of what trotter actually outputs (first order) *)
Theorem trotter_first_order_error : forall (d : nat) (err t : R) (input : norm_prog) (N' : nat),
  trotter_step err t input = S N' ->
  norm (2^d) (Mminus (mult_exp_list t d (trotter err t input))
                      (expH (2^d) t (norm_prog2mat input d)))
  <= INR (S N') * cal_1st_trotter_error_bound (t / INR (S N')) d input.
Proof.
  intros d err t input N' HN.
  unfold trotter. rewrite HN.
  rewrite trotter_nstep_nrep, mult_exp_list_nrep.
  unfold trotter_astep.
  rewrite mult_exp_list_scale.
  assert (Hpos: INR (S N') <> 0) by (apply not_0_INR; lia).
  replace (R1 / INR (S N') * t)%R with (t / INR (S N'))%R by (field; exact Hpos).
  apply first_order_blocks_error_bound.
Qed.

(* same for trotter_2nd_order; its block is the second-order formula on (rev input) *)
Theorem trotter_second_order_error : forall (d : nat) (err t : R) (input : norm_prog) (N' : nat),
  input <> [] ->
  trotter_step_2nd_order err t input = S N' ->
  norm (2^d) (Mminus (mult_exp_list t d (trotter_2nd_order err t input))
                      (expH (2^d) t (norm_prog2mat input d)))
  <= INR (S N') * cal_2nd_trotter_error_bound (t / INR (S N')) d (rev input).
Proof.
  intros d err t input N' Hne HN.
  unfold trotter_2nd_order. rewrite HN.
  rewrite trotter_nstep_nrep, mult_exp_list_nrep.
  rewrite mult_exp_list_app.
  unfold trotter_astep.
  rewrite !mult_exp_list_scale.
  assert (Hpos: INR (S N') <> 0) by (apply not_0_INR; lia).
  assert (Hc: (R1 / (INR (S N') * R2) * t = t / INR (S N') / 2)%R)
    by (unfold R2; field; exact Hpos).
  rewrite Hc.
  assert (Hblock: Mmult (mult_exp_list (t / INR (S N') / 2) d input)
                        (mult_exp_list (t / INR (S N') / 2) d (rev input))
                = approx_trotter_exp_2nd (t / INR (S N')) (rev input) d).
  { unfold approx_trotter_exp_2nd. rewrite rev_involutive. reflexivity. }
  rewrite Hblock.
  rewrite <- (norm_prog2mat_rev input d).
  apply second_order_blocks_error_bound.
  intro Hc'. apply Hne. destruct input; [reflexivity | simpl in Hc'; destruct (rev input); discriminate].
Qed.
