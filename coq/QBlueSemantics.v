(* This document contains the semantics of QBlue *) 

Require Import Reals.
Require Import Coq.Strings.String.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.VectorStates.
Require Import QBlue.QBlueSyntax.
Require Import QBlueType.
(* Local Open Scope nat_scope. 

Coercion INR : nat >-> R. *)
Definition create_sem (m:nat) (b:nat) : option (C * nat) :=
  if b <? m then Some (RtoC (sqrt (INR (b+1))), Nat.add b 1) else None.


Definition anni_sem (m:nat) (b:nat) : option (C * nat) :=
  if b =? 0 then None else Some (RtoC (sqrt (INR b)), Nat.sub b 1).

Local Open Scope nat_scope.

Inductive forall_map (P:psi -> psi -> Prop) : psi -> psi -> Prop :=
    forall_map_empty : forall_map P nil nil
  | forall_map_many: forall x y s1 s2, P ([x]) y -> forall_map P s1 s2 -> forall_map P (x::s1) (y++s2).

Definition nleft (f:nat -> nat) (n:nat) := fun i => f (i + n).

Fixpoint allFem (t:iota) (f:nat -> nat) :=
  match t with [] => 0
             | Fem::xl => f 0 + allFem xl (nleft f 1)
             | (Bos a)::xl => allFem xl (nleft f 1)
  end.

Definition ketCombine (n:nat) (f1 f2:nat -> nat) :=
  fun i => if i <? n then f1 i else f2 (i-n).

Fixpoint subcombine (n:nat) (a : (C * basisKet)) (qs : psi) : psi :=
  match qs with 
  | [] => []
  | (x,y)::xs => (Cmult (fst a) x, ketCombine n (snd a) y)::subcombine n a xs
  end.

Fixpoint combine (n:nat) (phi1 phi2: psi) : psi:=
  match phi1 with 
    | [] => []
    | x::xs => subcombine n x (combine n xs (phi2))
  end.

Inductive blue_sem : nat -> iota -> blueExp -> psi -> psi -> Prop := 
   s_id : forall n t s, blue_sem n t HId s s
 | f_anni_1: forall n s, anni_sem 2 (snd s 0) = None -> blue_sem n ([Fem]) HAnni ([s]) (nil)
 | f_anni_2: forall n s c m, anni_sem 2 (snd s 0) = Some (c,m)
               -> blue_sem n ([Fem]) HAnni ([s]) ([(fst s, (update (snd s) 0 m))])
 | f_crea_1: forall n s, create_sem 2 (snd s 0) = None -> blue_sem n ([Fem]) (HDag HAnni) ([s]) (nil)
 | f_crea_2: forall n s c m, create_sem 2 (snd s 0) = Some (c,m)
               -> blue_sem n ([Fem]) (HDag HAnni) ([s]) ([(fst s, (update (snd s) 0 m))])
 | b_anni_1: forall n j s, anni_sem j (snd s 0) = None -> blue_sem n ([Bos j]) HAnni ([s]) (nil)
 | b_anni_2: forall n j s c m, anni_sem j (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) HAnni ([s]) ([(fst s, (update (snd s) 0 m))])
 | b_crea_1: forall n j s, create_sem j (snd s 0) = None -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) (nil)
 | b_crea_2: forall n j s c m, create_sem j (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) ([(fst s, (update (snd s) 0 m))])
 | s_top: forall n t e s s1, forall_map (blue_sem n t e) s s1 -> blue_sem n t e s s1
 | s_ten: forall n t1 t2 e1 e2 w s1 s2, blue_sem n t1 e1 ([w]) s1 
                 -> blue_sem (n+allFem t1 (snd w)) t2 e2 ([(C1, nleft (snd w) (length t1))]) s2
                 -> blue_sem n (t1++t2) (HTensor e1 e2) ([w]) (combine (length t1) s1 s2)
 | s_app: forall n t e1 e2 s s1 s2, blue_sem n t e2 s s1 
                 -> blue_sem n t e1 s1 s2
                 -> blue_sem n t (HApp e1 e2) s s2
 | s_plus: forall n t e1 e2 s s1 s2, blue_sem n t e1 s s1 
                 -> blue_sem n t e2 s s2
                 -> blue_sem n t (HPlus e1 e2) s (s1++s2).

Inductive WFKet : iota -> basisKet -> Prop := 
  WFEmpty : forall s, WFKet nil s
 | WFManyF : forall xl s, s 0 < 2 -> WFKet xl (nleft s 1) -> WFKet (Fem::xl) s
 | WFManyB : forall m xl s, s 0 < m -> WFKet xl (nleft s 1) -> WFKet (Bos m::xl) s.

Definition WFState (t:iota) (s:psi) := forall e, In e s -> WFKet t (snd e).


(* Theorem: type soundness *)

Axiom fun_all_equal : forall (f c: rz_val), f = c \/ f <> c.

Lemma find_basis_elems_exists: forall n n' f fc i, exists m acc, find_basis_elems n n' f fc i m acc.
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply find_basis_empty.
  destruct IHi as [m [acc H]].
  assert (f = cut_n (lshift_fun (snd (fc i)) n') n \/ f <> cut_n (lshift_fun (snd (fc i)) n') n) by apply classic.
  destruct H0.
  exists (S m),(update acc m (fc i)). constructor; try easy.
  exists m,acc. constructor; try easy.
Qed.

Lemma assem_bool_exists: forall n n' i m f fc, exists mv fv, assem_bool n n' i f (Cval m fc) (Cval mv fv).
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply assem_bool_empty.
  destruct (IHi m f fc) as [m' [acc H]].
  destruct (find_basis_elems_exists n n' (cut_n (snd (f i)) n) fc m) as [mv [fv H1]].
  destruct mv.
  exists (S m'), ((update acc m' (f i))).
  eapply assem_bool_many_1; try easy. apply H1.
  destruct (assem_list (S mv) m' n (cut_n (snd (f i)) n) fv acc) eqn:eq1.
  exists n0,p.
  eapply assem_bool_many_2 with (mv := (S mv)); try easy. apply H. lia. apply H1. easy.
Qed.

Lemma simple_subst_ses: forall s i l, simple_ses (subst_locus s i l) -> (forall v, simple_ses (subst_locus s i v)).
Proof.
  intros.
  induction s. simpl in *. easy.
  simpl in *. inv H.
  unfold subst_range in *. destruct a. destruct p. inv H0.
  constructor.
  unfold simple_bound in *.
  unfold subst_bound in *.
  destruct b0. bdestruct (i =? v1); easy. easy.
  unfold simple_bound,subst_bound in *.
  destruct b. bdestruct (i =? v1); easy. easy.
  apply IHs. easy.
Qed.

Lemma simple_tenv_subst_right: forall T i l,
  simple_tenv (subst_type_map T i l) -> (forall v, simple_tenv (subst_type_map T i v)).
Proof.
  intros. unfold simple_tenv in *.
  intros. induction T; simpl in *. easy.
  destruct a0. simpl in *. destruct H0. inv H0.
  specialize (H (subst_locus l0 i l) b). 
  assert ((subst_locus l0 i l, b) = (subst_locus l0 i l, b) \/
    In (subst_locus l0 i l, b) (subst_type_map T i l)). left. easy.
  apply H in H0. eapply simple_subst_ses. apply H0.
  apply IHT. intros. apply H with (b := b0). right. easy.
  easy.
Qed.


Lemma simple_tenv_app_l: forall T T1, simple_tenv (T++T1) -> simple_tenv T.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. left. apply H0.
Qed.

Lemma simple_tenv_app_r: forall T T1, simple_tenv (T++T1) -> simple_tenv T1.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. right. apply H0.
Qed.

Lemma simple_tenv_app: forall T T1, simple_tenv T -> simple_tenv T1 -> simple_tenv (T++T1).
Proof.
  intros. unfold simple_tenv in *; intros.
  apply in_app_iff in H1. destruct H1. eapply H. apply H1.
  eapply H0. apply H1.
Qed.

Lemma bexp_extend: forall aenv b n l l1 v v' s sa, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: s++sa) b ((l ++ l1, v') :: s++sa).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2.
  inv HeqS2. constructor.
Qed.

Lemma bexp_extend_1: forall aenv b n l l1 v v' s, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: nil) b ((l ++ l1, v') :: nil).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2.
  inv HeqS2. constructor.
Qed.

Lemma qfor_sem_local: forall rmax aenv s e s' s1,
   @qfor_sem rmax aenv s e s' -> @qfor_sem rmax aenv (fst s, (snd s)++s1) e (fst s', (snd s')++s1).
Proof.
  intros. induction H using qfor_sem_ind'; simpl in *; try easy.
  constructor. apply let_sem_c with (n0 := n); try easy.
  destruct s; simpl in *.
  replace (s, s' ++ s1) with (fst ((s, q ++ s1)), s' ++ s1) by easy.
  apply let_sem_m with (W0 := W) (n0 := n); try easy.
  apply let_sem_q with (W'0 := W') (r0 := r) (v0 := v) (va'0 := va'); try easy.
  constructor. easy.
  constructor. easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  apply if_sem_cf. easy.
  apply (if_sem_q aenv W W' l l1 n n' (s++s1) (s'++s1) b e m f f' fc fc' fc''); try easy.
  apply bexp_extend with (aenv := aenv) (n := n); try easy.
  apply seq_sem with (s4 := (fst s0, snd s0 ++ s1)); try easy.
  apply for_sem.
  remember (h-l) as n. clear Heqn. clear H.
  generalize dependent s'.
  induction n; intros; simpl in *; try easy.
  inv H0.
  apply ForallA_nil.
  inv H0. apply IHn in H1.
  apply ForallA_cons with (s' := (fst s'0, snd s'0 ++ s1)); try easy.
Qed.

Lemma simple_tenv_ses_system: forall rmax t aenv T e T',
  simple_tenv T -> @locus_system rmax t aenv T e T' -> simple_tenv T'.
Proof.
  intros. induction H0; simpl in *; try easy.
  apply simple_tenv_app_l in H as X1.
  apply simple_tenv_app_r in H as X2.
  apply simple_tenv_app; try easy. apply IHlocus_system. easy.
  apply IHlocus_system. rewrite simple_env_subst; try easy.
  apply IHlocus_system; try easy.
  apply IHlocus_system. unfold simple_tenv in *.
  intros. simpl in *. destruct H3. inv H3.
  specialize (H ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
    In ((y, BNum 0, BNum n) :: a, CH) T ). left. easy.
  apply H in H3. inv H3. easy. eapply H. right. apply H3.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  apply IHlocus_system; try easy.
  apply IHlocus_system2; try easy.
  apply IHlocus_system1; try easy.
  apply simple_tenv_subst_right with (v := h) in H. easy.
Qed.

Theorem type_right_matrix: forall ia e, typing ia e (H, ia) ->  rewrites_recur ia (HDag e) e.
Proof.
  intros. induction H; try easy.
  apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [sa [sb [X1 [X2 X3]]]].
  destruct s0; simpl in * ; subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H as X1.
  rewrite <- app_assoc in *.
  destruct (IHlocus_system X1 W (s0,q0) (sb++s2) sa H3 H2) as [sc [Y1 [Y2 Y3]]]; simpl in *; subst.
  exists (sc++sb). rewrite app_assoc. split; try easy.
  split.
  apply qfor_sem_local with (s1 := sb) in Y2; try easy.
  apply env_state_eq_app_join; try easy.
  inv H2. inv H0. exists nil. simpl. split; try easy. split. constructor. constructor.
  inv H4. rewrite H1 in H11. inv H11. rewrite simple_env_subst in *; try easy.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]. exists sa. split. easy.
  split. apply let_sem_c with (n0 := n); try easy. easy.
  apply simp_aexp_no_eval in H11. rewrite H11 in *. easy.
  inv H4. apply type_aexp_mo_no_simp in H0. rewrite H0 in *; try easy.
  unfold update_cval in *. simpl in *.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]; simpl in *.
  exists sa. split; try easy. split. apply let_sem_m with (W1 := W0) (n0 := n); try easy.
  easy.
  inv H4. inv H3. simpl in *. inv H6.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H3. inv H3.
  specialize (H ((y, BNum 0, BNum n) :: a0) CH).
  assert (((y, BNum 0, BNum n) :: a0, CH) = ((y, BNum 0, BNum n) :: a0, CH) \/
    In ((y, BNum 0, BNum n) :: a0, CH) T). left. easy.
  apply H in H3.
  inv H3. easy. apply H with (b:= b). right. easy.
  assert (env_state_eq ((l, CH) :: T) ((l, va') :: l2)).
  constructor; try easy.
  unfold build_state_ch in *. destruct a; try easy.
  destruct (build_state_pars m n v (to_sum_c m n v b) b) eqn:eq1; try easy. inv H14. constructor.
  destruct (IHlocus_system H3 (AEnv.add x (r, v) W)
     (W', s') s2 ((l, va') :: l2) H4 H15) as [sa [X1 [X2 X3]]].
  simpl in *; subst.
  exists sa. split; try easy.
  split. apply let_sem_q with (W'0 := W') (r0 := r) (v0 := v) (va'0 := va'); try easy.
  easy.
  inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l, Nval ra ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
  inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l ++ l0, Cval m ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
  inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Hval (eval_to_had n r))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
  inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Nval C1 (eval_to_nor n bl))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
  inv H4. apply IHlocus_system in H11; try easy.
  destruct H11 as [sa [X1 [X2 X3]]].
  destruct s; simpl in *; subst. exists sa.
  split; try easy. split; try constructor; try easy.
  rewrite H1 in H10. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
  inv H3. rewrite H1 in H8. easy.
  exists s1. split; try easy.
  split. apply if_sem_cf. easy. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
  inv H2.  inv H8. inv H9. inv H3.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *; try easy. destruct H2; try easy.
  inv H2.
  specialize (H (l ++ a) CH).
  assert ((l ++ a, CH) = (l ++ a, CH) \/ False).
  left. easy. apply H in H2.
  apply simple_ses_app_r in H2. easy.
  apply type_bexp_only with (t := (QT n0, l0)) in H0; try easy.
  inv H0. apply app_inv_head_iff in H4; subst.
  specialize (IHlocus_system H2 W (W', (l1, fc') :: s') s2 ([(l1, fc)])); simpl in *.
  assert (env_state_eq ((l1, CH) :: nil) ((l1, fc) :: nil)).
  constructor; try easy. constructor.
  inv H15. constructor.
  simpl in *.
  destruct (IHlocus_system H0 H16) as [sa [X1 [X2 X3]]].
  inv X3. inv H7. inv H8. simpl in *. inv X1.
  exists ([(l ++ l1, fc'')]); simpl in *.
  split. easy.
  split. apply (if_sem_q env W W' l l1 n n' nil nil b e m bl f' fc (Cval m0 bl0) fc''); try easy.
  apply bexp_extend_1 with (aenv := env) (n := n) (s := s2); try easy.
  constructor. constructor.
  inv H17; try constructor.
  apply simple_tenv_ses_system in H1_ as X1; try easy. inv H2.
  apply IHlocus_system1 in H6; try easy.
  destruct H6 as [sa [Y1 [Y2 Y3]]]. destruct s3 in *; simpl in *; subst.
  apply IHlocus_system2 in H8; try easy.
  destruct H8 as [sb [Y4 [Y5 Y6]]]. destruct s in *; simpl in *; subst.
  exists sb. split; try easy.
  split; try easy.
  apply seq_sem with (s4 := (s0,sa)); try easy.
  inv H2. assert (h-l = 0) by lia. rewrite H2 in *. inv H11.
  exists s1. split; try easy. split; try easy.
  simpl in *. constructor. rewrite H2. constructor.
  inv H5.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H5 in *. clear H5. clear h.
  clear H0. clear Heqna.
  generalize dependent s.
  induction na;intros;simpl in *.
  inv H14.
  replace (l+0) with l by lia.
  exists s1. split; try easy. split. constructor.
  replace (l-l) with 0 by lia. constructor. easy.
  inv H14.
  assert (forall v : nat,
        l <= v < l + na ->
        @locus_system rmax q env (subst_type_map T i v)
          (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H2. lia.
  assert ((forall v : nat,
        l <= v < l + na ->
        simple_tenv (subst_type_map T i v) ->
        forall (W : stack) (s : state) (s2 : list (locus * state_elem))
          (s1 : qstate),
        env_state_eq (subst_type_map T i v) s1 ->
        @qfor_sem rmax env (W, s1 ++ s2) (If (subst_bexp b i v) (subst_pexp e i v))
          s ->
        exists s1' : list (locus * state_elem),
          snd s = s1' ++ s2 /\
          @qfor_sem rmax env (W, s1) (If (subst_bexp b i v) (subst_pexp e i v))
            (fst s, s1') /\ env_state_eq (subst_type_map T i (v + 1)) s1')).
  intros. apply H3; try lia; try easy.
  destruct (IHna H0 H7 s' H5) as [sa [X1 [X2 X3]]].
  assert (l <= l+ na < l + S na) by lia.
  apply simple_tenv_subst_right with (v := (l+na)) in H as Y2.
  destruct s'; simpl in *; subst.
  destruct (H3 (l + na) H8 Y2 s0 s s2 sa X3 H6) as [sb [X4 [X5 X6]]].
  exists sb. split; try easy.
  split. constructor.
  replace ((l + S na - l)) with (S na) by lia.
  apply ForallA_cons with (s' := (s0, sa)); try easy. inv X2.
  replace ((l + na - l)) with na  in H17 by lia. easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
Qed.

Theorem type_soundness: forall ia e t n s, typing ia e t -> WFState ia s -> exists s', blue_sem n ia e s s' /\ WFState ia s'.
Proof.
  intros. induction H; try easy.
  destruct s0; simpl in *.
  apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [s1 [s2 [X1 [X2 X3]]]].
  subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H3 as X1.
  apply type_sem_local with (q := q) (env := env) (T := T) (T' := T') in H4; try easy.
  destruct H4 as [sa [Y1 [Y2 Y3]]]; subst. destruct s'; simpl in *; subst.
  apply IHlocus_system in Y2; try easy. destruct Y2 as [A1 [A2 A3]].
  split. apply simple_tenv_app; try easy.
  apply simple_tenv_app_r in H3; try easy. split. easy.
  apply env_state_eq_app_join; try easy.
  inv H4. easy.
  inv H6.
  rewrite H0 in H13. inv H13.
  rewrite simple_env_subst in IHlocus_system; try easy.
  apply freeVars_pexp_in with (v := n) in H2 as X1; try easy.
  specialize (IHlocus_system X1 H3 s' s H4 H5 H14). easy.
  apply simp_aexp_no_eval in H13. rewrite H0 in *. easy.
  inv H6. 
  apply type_aexp_mo_no_simp in H. rewrite H in *. easy.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H7. inv H7. easy.
  apply AEnv.add_3 in H7; try lia.
  apply H2 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  specialize (IHlocus_system H6 H3 (W, s'0) (update_cval s x n)).
  simpl in *.
  assert (kind_env_stack
                     (AEnv.add x (Mo MT) env)
                     (AEnv.add x n (fst s))).
  unfold kind_env_stack. split. intros.
  bdestruct (x0 =? x); subst.
  exists n. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H7; try easy.
  apply H5 in H7. destruct H7.
  exists x1. apply AEnv.add_2. lia. easy. lia.
  intros.
  bdestruct (x0 =? x); subst.
  apply AEnv.add_1. easy.
  destruct H7.
  apply AEnv.add_3 in H7; try easy.
  assert (AEnv.In x0 (fst s)). exists x1. easy.
  apply H5 in H9.
  apply AEnv.add_2. lia. easy. lia.
  destruct (IHlocus_system H4 H7 H14) as [Y1 [Y2 Y3]].
  split. easy.
  split; try easy.
  inv H6.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H7. inv H7. easy.
  apply AEnv.add_3 in H7; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H7. inv H7.
  specialize (H3 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H3 in H7.
  inv H7. easy. apply H3 with (b:= b). right. easy.
  unfold build_state_ch in *. destruct va; try easy.
  destruct (build_state_pars m n0 v (to_sum_c m n0 v b) b); try easy.
  inv H15.
  inv H4.
  specialize (IHlocus_system H6 H7 (W', s'0) (AEnv.add x (r, v) W, (l0, Cval n1 p) :: s0)).
  assert (env_state_eq ((l0, CH) :: T) ((l0, Cval n1 p) :: s0)).
  constructor. easy. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x (r, v) W)).
  unfold kind_env_stack in *. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r, v). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H8; try lia.
  apply H5 in H8. destruct H8.
  exists x1. apply AEnv.add_2; try lia. easy. simpl in *.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  assert (AEnv.In (elt:=R * nat) x0 W).
  destruct H8. exists x1. apply AEnv.add_3 in H8; try lia. easy.
  apply H5 in H12. apply AEnv.add_2. lia. easy.
  destruct (IHlocus_system H4 H8 H16) as [Y1 [Y2 Y3]]. split; try easy.
  inv H5; simpl in *. inv H1. inv H7. 
  split. easy. split;try easy. constructor. constructor. constructor.
  inv H1. inv H13.
  inv H5. inv H1. inv H13.
  inv H1. inv H7.
  apply app_inv_head_iff in H9. subst.
  split. easy. split. easy.
  constructor. constructor. constructor.
  inv H5. inv H1. inv H8.
  split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := TNor).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
  inv H1. inv H14.
  inv H5. inv H1. inv H14.
  inv H1. inv H8. split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := THad).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
  inv H6.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  specialize (IHlocus_system H6 H3 s' s H4 H5 H13). split; easy.
  rewrite H0 in H12. inv H12.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
  inv H5. rewrite H0 in H10. inv H10.
  easy.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
  inv H5. apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  split. easy. inv H1. inv H7.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *; try easy. destruct H5; try easy.
  inv H5.
  specialize (H3 (l ++ a) CH).
  assert ((l ++ a, CH) = (l ++ a, CH) \/ False).
  left. easy. apply H3 in H5.
  apply simple_ses_app_r in H5. easy.
  apply type_bexp_only with (t := (QT n0, l0)) in H; try easy.
  inv H. apply app_inv_head_iff in H13; subst.
  specialize (IHlocus_system H1 H5
          (W', (l2, fc') :: s'0) (W, (l2, fc) :: nil)).
  assert (env_state_eq ((l2, CH) :: nil)
                     (snd (W, (l2, fc) :: nil))).
  constructor; try easy. constructor.
  inv H11. constructor.
  simpl in *.
  destruct (IHlocus_system H H4 H14) as [X1 X2].
  inv X2. constructor; try easy.
  inv H7. inv H15.
  constructor. constructor.
  inv H16; try constructor.
  inv H5.
  assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. left. easy.
  assert (freeVarsNotCPExp env e2).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. right. easy.
  destruct (IHlocus_system1 H5 H3 s1 s H1 H4 H10) as [X1 [X2 X3]].
  apply kind_env_stack_equal with (env := env) in X2 as X4; try easy.
  destruct (IHlocus_system2 H6 X1 s' s1 X3 X4 H12) as [Y1 [Y2 Y3]].
  split; try easy. split; try easy.
  apply AEnvFacts.Equal_trans with (m' := fst s1); try easy.
  inv H4. assert (h-l = 0) by lia. rewrite H4 in *. inv H13.
  split; try easy.
  split. eapply simple_tenv_subst_right. apply H3.
  inv H7.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H7 in *. clear H7. clear h.
  assert (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v))) as Y1.
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff in H7. 
  bdestruct (x =? i); subst.
  assert (AEnv.In i env). exists (Mo t). easy. easy.
  destruct H7.
  apply in_app_iff. left.
  apply list_sub_not_in; try easy.
  apply freeVarsBExp_subst in H7. easy.
  apply in_app_iff. right.
  apply list_sub_not_in; try easy.
  apply freeVarsPExp_subst in H7. easy.
  clear H. clear H2. clear Heqna.
  generalize dependent s'.
  induction na;intros;simpl in *.
  inv H16. split. easy.
  replace (l+0) with l by lia. easy.
  inv H16.
  intros. apply H4; try lia; try easy.
  destruct (IHna H H8 s'0 H2) as [X1 X2].
  assert (l <= l+ na < l + S na) by lia.
  apply simple_tenv_subst_right with (v := (l+na)) in H3 as Y2.
  apply kind_env_stack_equal with (env := env) in X1 as X4; try easy.
  destruct (H4 (l + na) H9 (Y1 (l+na)) Y2 s' s'0 X2 X4 H7) as [X7 [X8 X9]].
  split.
  apply AEnvFacts.Equal_trans with (m' := fst s'0); try easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
Qed.
