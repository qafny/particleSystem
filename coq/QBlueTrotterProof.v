(* Define the trotterization step, Lie-Trotter fomular, qdrift *)
Require Import QuantumLib.Matrix.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueTrotter.

(**** Approximate central value using 1st-order std Trotter
Approx = exp(-itH_k) exp(-itH_{k-1}) ... exp(-itH_{1})
d: d paulis in one tensor product ****)
Fixpoint mult_exp_list (t : R) (d : nat) (l : lowprog) : Square (2^d) :=
  match l with
  | [] => I (2^d)
  | aten :: tl => Mmult (mult_exp_list t d tl) (expH (2^d) t (lowprog2mat [aten] d))
  end.

(* Approx = exp(-itH_k) exp(-itH_{k-1}) ... exp(-itH_{1})
d: d paulis in one tensor product 
k: first k pauli strings go to Approx *)
Definition approx_mult_exp (t : R) (k d : nat) (hlist : lowprog) : Square (2^d) :=
  mult_exp_list t d (firstn k hlist).


Lemma mult_exp_list_app : forall t d (l1 l2 : lowprog),
  mult_exp_list t d (l1 ++ l2)
  = Mmult (mult_exp_list t d l2) (mult_exp_list t d l1).
Proof.
  intros t d l2.
  induction l2 as [| a l2 IH].
  intro l1.
  - cbn. (* [] ++ l1 *)
    (* X * I = X *)
    rewrite Mmult_1_r. reflexivity. admit.
  - cbn. (* (a::l1) ++ l2 *)
    (* rewrite IH .
    (* exp1 a * (A * B) = (exp1 a * A) * B *)
    rewrite Mmult_assoc.
    reflexivity. *)
Admitted.


(* exp(-it * lp) *)
Definition exp_sum (t : R) (d : nat) (hlist : lowprog) : Square (2^d) :=
  expH (2^d) t (lowprog2mat hlist d).  

(* Define transitional term for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{k1})) *)
Definition approx_transit_exp_aterm (t : R) (k d : nat) (hlist : lowprog) : Square (2^d) :=
  let term_sum := skipn k hlist in 
    Mmult (exp_sum t d term_sum) (approx_mult_exp t k d hlist).

(* approx_mult_exp(lp::a) = exp(a) x approx_mult_exp(lp) *)
Theorem approx_mult_exp_succ :
  forall (t : R) (d n : nat) (hlist : lowprog) (a : lowprog_ten),
  nth_error hlist n = Some a 
  -> approx_mult_exp t (S n) d hlist
  = Mmult (expH (2^d) t (lowprog2mat [a] d)) (approx_mult_exp t n d hlist).
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
  rewrite Mmult_1_l.
  reflexivity.
  admit.
Admitted.


(* transitional terms for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{1})) 
- exp(-it* (sum_{k}^N Hi) x exp(-itH_{k+1} x ... x exp(-itH_{1}))  *)
Definition expand_transit_term (t:R) (k d:nat) (hlist:lowprog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => Mminus (approx_transit_exp_aterm t k d hlist) (approx_transit_exp_aterm t k' d hlist)
  end.

(* transitional terms for proving trotterization:
exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi)) *)
Definition expand_aterm (t : R) (k d : nat) (hlist : lowprog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => match (nth_error hlist k') with
    | None => Zero
    | Some a => 
      let term_sum1 := skipn k hlist in
      let term_sum2 := skipn k' hlist in
        Mminus (Mmult (exp_sum t d term_sum1) (expH (2^d) t (lowprog2mat [a] d)))
        (exp_sum t d term_sum2) 
      end
    end.


(* transitional terms for proving trotterization:
[sum_{k+1}^N Hi, Hk] *)
Definition expand_aterm_approx (k d : nat) (hlist : lowprog) : Square (2^d) :=
  match k with
  | 0 => Zero
  | S k' => match (nth_error hlist k') with
    | None => Zero
    | Some a => 
      let term_sum := skipn k hlist in 
      Mminus (Mmult (lowprog2mat term_sum d) (lowprog2mat [a] d))
      (Mmult (lowprog2mat [a] d)  (lowprog2mat term_sum d))
      end
    end.

(* transitional terms for proving trotterization *)
Fixpoint expand_1st_trotter_error_helper (t : R) (k d : nat) (hlist : lowprog) : Square (2^d) :=
  match k with 
  | 0 => Zero
  | S k' => (expand_transit_term t k d hlist) 
  .+ (expand_1st_trotter_error_helper t k' d hlist) 
  end.
  
Definition expand_1st_trotter_error (t : R) (d : nat) (hlist : lowprog) : Square (2^d) :=
  let N := length hlist in 
  expand_1st_trotter_error_helper t N d hlist.

(* norm each term in expand_1st_trotter_error *)  
Fixpoint expand_1st_trotter_error_1est_helper (t : R) (k d : nat) (hlist : lowprog) : R :=
  match k with 
  | 0 => 0
  | S k' => norm (2^d) (expand_transit_term t k d hlist) 
  + (expand_1st_trotter_error_1est_helper t k' d hlist) 
  end.
  
Definition expand_1st_trotter_error_1st (t : R) (d : nat) (hlist : lowprog) : R :=
  let N := length hlist in 
  expand_1st_trotter_error_1est_helper t N d hlist.


(* Gold error: || e^{-i H t} - PI_i (e^{-i Hi t}) || *)
Definition cal_1st_trotter_error (t : R) (lp : lowprog) : R :=
  match lp with 
  | [] => 0
  | (_, d, _) :: rem =>
    let exp_mat_gold := approx_transit_exp_aterm t (length lp) d lp in 
    let exp_mat_approx := approx_transit_exp_aterm t 0%nat d lp in
    norm (2^d) (Mminus exp_mat_gold exp_mat_approx)
  end.  


(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator_tt (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-myC1) [ten_app_ten h2 h1]).

Definition commutator_st (h1 : lowprog) (h2 : lowprog_ten) : lowprog :=
  let l1 := plus_app_ten h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (ten_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition commutator_ts (h1 : lowprog_ten) (h2 : lowprog) : lowprog :=
  let l1 := ten_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_ten h2 h1) in
  plus_plus_plus l1 l2.


(* [sum_{i=γ1+1, n} H_i, H_γ1], γ1 starts from 0 *)
(* Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with 
  | [] => []
  | h :: rem => commutator_st rem h
  end. *)

(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
(* k: γ1, start from 0; d: # of paulis in one string; hlist: trottered input lowprog *) 
Fixpoint trotter_error_bound_helper (k d : nat) (hlist : lowprog) : R :=
  match k with
  | 0 => 0
  | S k' => let comm_sum := expand_aterm_approx k d hlist in
       (norm (2 ^ d) comm_sum) + (trotter_error_bound_helper k' d hlist)
  end.

(* 1st-order error: t^2/2 * ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] *)
Definition cal_1st_trotter_error_bound (t : R) (hlist : lowprog) : R :=
  let gamma := length hlist in
  match hlist with
  | [] => 0
  | (_, d, _) :: _ => (t*t/2) * (trotter_error_bound_helper gamma d hlist)
  end. 

(* TODO: check Hermitian *)
(* norm(exp(A+B) - exp(A) exp(B)) <= [A, B] *)
Theorem expmat_commnute_ineq: forall (n : nat) (m1 m2 : Square n) (t : R),
  norm n (Mminus (Mmult (expH n t m2) (expH n t m1)) (expH n t (m1 .+ m2)))
  <= (t*t/2) * (norm n (Mminus (Mmult m2 m1) (Mmult m1 m2))).
Proof.
  
Admitted.


Theorem matnorm_sum_triangle_ineq: forall (n : nat) (m1 m2 : Square n),
  norm n (Mplus m1 m2) <= (norm n m1) + (norm n m2).
Proof.
Admitted.


Theorem  zero_norm_eqzero: forall (d: nat),
  norm d Zero = 0.
Proof.
Admitted.

Axiom zero_expH_isI: forall (d : nat) (t : R),
  expH d t Zero = I d.


Theorem matnorm_mult_triangle_ineq: forall (n : nat) (m1 m2 : Square n),
  norm n (Mmult m1 m2) <= (norm n m1) * (norm n m2).
Proof.
Admitted.


Theorem unitarymat_norm_eqone: forall (d : nat) (m: Square d),
  Mmult m (m †) = I d
  -> norm d m = 1.
Proof.
Admitted.

Lemma Mplus_opp_0 : forall (m n : nat) (A : Matrix m n), A .+ (Mopp A) = Zero.
Proof. 
  intros. lma.
Qed. 


(* sublemma for proving 1st trotter:
norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k} x ... x exp(-itH_{1})) 
- exp(-it* (sum_{k}^N Hi) x exp(-itH_{k+1} x ... x exp(-itH_{1}))) 
<= norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi))) 
*)
Theorem expand_term_norm_bound: forall (t : R) (k d:nat) (hlist:lowprog),
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
      set (A := Mmult (exp_sum t d (skipn (S k) hlist)) (expH (2 ^ d) t (lowprog2mat [a] d))).
      set (B := exp_sum t d (skipn k hlist)).
      set (D := approx_mult_exp t k d hlist).
      rewrite <- Mscale_mult_dist_l.
      rewrite <- Mmult_plus_distr_r.
      eapply Rle_trans.
      + apply (matnorm_mult_triangle_ineq (2 ^ d) (A .+ - C1 .* B) D). 
      + assert (H2: norm (2 ^ d) D = 1). 
        {admit. } 
        rewrite H2. 
        rewrite Rmult_1_r. 
        apply Rle_refl.
    -- apply nth_error_None in Hnth.
      assert (Hdr: skipn (S k) hlist = []).
       {apply skipn_all2. auto. }
      assert (Hdr1: skipn k hlist = []).
       {apply skipn_all2. auto. }
      rewrite Hdr, Hdr1.
      unfold exp_sum, lowprog2mat.
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
Admitted.


(* sublemma for proving 1st trotter:
 norm(exp(-it* (sum_{k+1}^N Hi) x exp(-itH_{k})) - exp(-it* (sum_{k}^N Hi))
 <= norm([sum_{k+1}^N Hi, H_k]) *)
Theorem expand_term_norm_bound1: forall (t : R) (k d : nat) (hlist:lowprog),
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
    set (m1 := lowprog2mat [a] d).
    set (m2 := lowprog2mat l2 d).
    assert (H3: lowprog2mat (a :: l2) d = m1 .+ m2 ).
    {
      destruct a as [[amp n] f]. simpl.
      subst m1 m2.
      cbn [lowprog2mat].
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


(* Trotterization: error bound for the first-order Lie-Trotter formula *)
(* A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem first_trotter_error_bound: forall (lp: lowprog) (t err err_bound : R),
  err = cal_1st_trotter_error t lp
  -> err_bound = cal_1st_trotter_error_bound t lp 
  -> err <= err_bound.
Proof.
  intros lp t err err_bound H H1.
  subst err.
  unfold cal_1st_trotter_error.
  destruct lp as [| l lpa].

  (* lp is [] *)
  - subst err_bound. simpl. unfold Rle. right. ring.

  - (* lp has at least one tensor term *)
  remember (l::lpa) as lp' eqn:Hlp.
  destruct l as [[amp d] f].
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

  -- admit. 
  -- admit. 

    (* apply WF_plus.
    auto with wf_db. 
    -- by_cell. lca *)
  

Admitted.


(**** Approximate central value using 2nd-order std Trotter ****)
(* Approx = exp(-it/2 H_1)exp(-it/2 H_2) ... exp(-it/2 H_n)exp(-it/2 H_{n-1}) ... *)
Definition approx_trotter_exp_2nd (t : R) (hlist : lowprog) (d : nat) : Square (2^d) := 
  let term1 := mult_exp_list (t/2) d (rev hlist) in
  let term2 := mult_exp_list (t/2) d hlist in
  Mmult term1 term2.

(* Gold error for 2nd-order trotter:
n: # of paulis in one pauli string *)
Definition cal_2nd_trotter_error (t : R) (lp : lowprog) : R :=
  match lp with 
  | [] => 0
  | (_, n, _) :: rem =>
    let exp_mat_gold := expH (2^n) t (lowprog2mat lp n) in 
    let exp_mat_approx := approx_trotter_exp_2nd t lp n in
    norm (2^n) (Mplus exp_mat_approx (scale (-R1) exp_mat_gold))
  end.


(* Tight error bound for the second-order Suzuki formula. *)
Definition commutator_ss (h1 : lowprog) (h2 : lowprog) : lowprog :=
  let l1 := plus_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition suzuki_comm_sum_helper (hlist : lowprog) : (lowprog * lowprog) :=
  match hlist with 
  | [] => ([], [])
  | x :: rem => 
    let t1 := commutator_ss rem (commutator_st rem x) in
    let t2 := commutator_ts x (commutator_ts x rem) in (t1, t2)
    end.

Fixpoint suzuki_error_bound_helper (n : nat) (t: R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | x :: ax => let (term1, term2) := suzuki_comm_sum_helper hlist in
      let t1 := lowprog2mat term1 n in
      let t2 := lowprog2mat term2 n in
      Rplus (Rplus (Rdiv ((norm (2 ^ n) t1) * (pow t 3)) 12)
                   (Rdiv ((norm (2 ^ n) t2) * (pow t 3)) 24))
            (suzuki_error_bound_helper n t ax)
  end.

(* 2nd-order error *)
Definition cal_2nd_trotter_error_bound (t : R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | (_, n, _) :: _ => suzuki_error_bound_helper n t hlist
  end.


Theorem second_trotter_error_bound: forall (lp: lowprog) (t err err_bound : R),
  err = cal_2nd_trotter_error t lp
  -> err_bound = cal_2nd_trotter_error_bound t lp 
  -> err <= err_bound.
Proof.
Admitted.
