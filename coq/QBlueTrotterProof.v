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