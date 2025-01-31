Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
Require Import MuQSyntax.
Require Import MuQSem.
Require Import MuQType.

Local Open Scope nat_scope.

(* This document contains MuQ theorem files. *)

(* We first define the values *)
Fixpoint isMatrix (e:exp) :=
   match e with
             | Trans a => isMatrix a
             | Anni s c t tf => true 
             | Plus al => forallb (fun x => isMatrix x) al
             | Tensor bl => forallb (fun x => isMatrix x) bl
             | _ => false
   end.

Fixpoint value (e:exp) :=
  match e with Var x => true
             | Val c => true
             | St s t => true
             | Zero tl => true
             | Trans a => value a
             | Lambda x t e => true
             | Mu x t e => true
             | _ => isMatrix e
  end.

(* The type progress theorem. For every well-typed expression, there exists a step. *)
Theorem type_progress: forall g e1 t, typing g e1 t 
   -> value e1 = true \/ exists e2, equiv e1 e2 /\ (value e2 = true \/ exists e3, sem e2 e3).
Proof.
  intros.
  induction H; intros.
 - left. easy.
 - left. easy.
 - left. easy.
 - left. easy.
 - left. easy.
 - left. easy.
 - left. easy.
 - destruct IHtyping. left. easy.
   destruct H0 as [e1 [X1 X2]].
   destruct X2.
   apply tpar with (g := g) (t := t) in X1 as X2; try easy; try easy.
   
 exists (St s t). split. apply equiv_self.
   left; easy.
 - exists (Anni j c t tf). split. apply equiv_self.
   left; easy.
 - exists (Lambda y t ea). split. apply equiv_self.
   left; easy.
 - exists (Mu y t ea). split. apply equiv_self.
   left; easy.
 - destruct IHtyping as [e1 [X1 X2]].
   destruct X2.
Admitted.

(* The following two theorems are the type preservation theorems. One for the type preservation in equivalence,
   and the other for type preservation for semantic reductions. *)

Theorem type_preservation_1: forall g e1 e2 t, typing g e1 t -> equiv e1 e2 -> exists g', typing g' e2 t.
Proof.
  intros. generalize dependent t. generalize dependent g. generalize dependent e2.
  generalize dependent W.
  induction H1; intros;simpl in *; subst; try easy.
- apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [sa [sb [X1 [X2 X3]]]].
  destruct s0; simpl in * ; subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H as X1.
  rewrite <- app_assoc in *.
  destruct (IHlocus_system X1 W (s0,q0) (sb++s2) sa H3 H2) as [sc [Y1 [Y2 Y3]]]; simpl in *; subst.
  exists (sc++sb). rewrite app_assoc. split; try easy.
  split.
  apply qfor_sem_local with (s1 := sb) in Y2; try easy.
  apply env_state_eq_app_join; try easy.
- inv H2. inv H0. exists nil. simpl. split; try easy. split. constructor. constructor.
- inv H4. rewrite H1 in H11. inv H11. rewrite simple_env_subst in *; try easy.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]. exists sa. split. easy.
  split. apply let_sem_c with (n0 := n); try easy. easy.
  apply simp_aexp_no_eval in H11. rewrite H11 in *. easy.
- inv H4. apply type_aexp_mo_no_simp in H0. rewrite H0 in *; try easy.
  unfold update_cval in *. simpl in *.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]; simpl in *.
  exists sa. split; try easy. split. apply let_sem_m with (W1 := W0) (n0 := n); try easy.
  easy.
- inv H4. inv H3. simpl in *. inv H6.
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
- inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l, Nval ra ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l ++ l0, Cval m ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Hval (eval_to_had n r))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Nval C1 (eval_to_nor n bl))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
- inv H4. apply IHlocus_system in H11; try easy.
  destruct H11 as [sa [X1 [X2 X3]]].
  destruct s; simpl in *; subst. exists sa.
  split; try easy. split; try constructor; try easy.
  rewrite H1 in H10. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
- inv H3. rewrite H1 in H8. easy.
  exists s1. split; try easy.
  split. apply if_sem_cf. easy. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
- inv H2.  inv H8. inv H9. inv H3.
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
- apply simple_tenv_ses_system in H1_ as X1; try easy. inv H2.
  apply IHlocus_system1 in H6; try easy.
  destruct H6 as [sa [Y1 [Y2 Y3]]]. destruct s3 in *; simpl in *; subst.
  apply IHlocus_system2 in H8; try easy.
  destruct H8 as [sb [Y4 [Y5 Y6]]]. destruct s in *; simpl in *; subst.
  exists sb. split; try easy.
  split; try easy.
  apply seq_sem with (s4 := (s0,sa)); try easy.
- inv H2. assert (h-l = 0) by lia. rewrite H2 in *. inv H11.
  exists s1. split; try easy. split; try easy.
  simpl in *. constructor. rewrite H2. constructor.
- inv H5.
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


Theorem type_preservation_2: forall g e1 e2 t, typing g e1 t -> sem e1 e2 -> exists g', typing g' e2 t.
Proof.
  intros. generalize dependent g. generalize dependent t.
  induction H; intros;simpl in *; subst.
 -
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
 -
  inv H4. easy.
 -
  inv H6.
  rewrite H0 in H13. inv H13.
  rewrite simple_env_subst in IHlocus_system; try easy.
  apply freeVars_pexp_in with (v := n) in H2 as X1; try easy.
  specialize (IHlocus_system X1 H3 s' s H4 H5 H14). easy.
  apply simp_aexp_no_eval in H13. rewrite H0 in *. easy.
 -
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
 -
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
 -
  inv H5; simpl in *. inv H1. inv H7. 
  split. easy. split;try easy. constructor. constructor. constructor.
  inv H1. inv H13.
 - 
  inv H5. inv H1. inv H13.
  inv H1. inv H7.
  apply app_inv_head_iff in H9. subst.
  split. easy. split. easy.
  constructor. constructor. constructor.
 -
  inv H5. inv H1. inv H8.
  split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := TNor).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
  inv H1. inv H14.
 -
  inv H5. inv H1. inv H14.
  inv H1. inv H8. split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := THad).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
 -
  inv H6.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  specialize (IHlocus_system H6 H3 s' s H4 H5 H13). split; easy.
  rewrite H0 in H12. inv H12.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
 - 
  inv H5. rewrite H0 in H10. inv H10.
  easy.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
 -
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
 -
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
 -
  inv H4. assert (h-l = 0) by lia. rewrite H4 in *. inv H13.
  split; try easy.
 -
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
  assert (forall v : nat,
        l <= v < l + na ->
        @locus_system rmax q env (subst_type_map T i v) (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H1. lia.
  assert ((forall v : nat,
        l <= v < l + na ->
        freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v)) ->
        simple_tenv (subst_type_map T i v) ->
        forall (s' : state) (s : stack * qstate),
        env_state_eq (subst_type_map T i v) (snd s) ->
        kind_env_stack env (fst s) ->
        @qfor_sem rmax env s (If (subst_bexp b i v) (subst_pexp e i v)) s' ->
        simple_tenv (subst_type_map T i (v + 1)) /\
        AEnv.Equal (fst s) (fst s') /\
        env_state_eq (subst_type_map T i (v + 1)) (snd s'))).
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
