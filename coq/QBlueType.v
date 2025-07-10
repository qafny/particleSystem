(*  the rewrite rules and typing system of QBlue *)

Require Import List.
Import ListNotations.
Require Import QuantumLib.Complex.
Require Import QuantumLib.VectorStates.
Require Import QBlue.QBlueSyntax.

(*
(* To make sure all programs are in canonical forms
e.g., only the followings are allowed:
a, a+, (any e1) + (any e2),
(e1 e2)⊗e3, e1(e2⊗e3) *)
Inductive canonicalCheck : bool -> H -> Prop := 
  | canonicalCheckAnni: forall c s m f, canonicalCheck f (HAnni c s m)
  | canonicalCheckHDag: forall c s m f, canonicalCheck f (HDag (HAnni c s m)) 
  (* within dagger only HAnni is allowed. *)
  | canonicalCheckHTensor: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HTensor e1 e2)
  | canonicalCheckHPlus: forall e1 e2 f, canonicalCheck f e1 -> canonicalCheck f e2
    -> canonicalCheck false (HPlus e1 e2)
  | canonicalCheckHApp: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HApp e1 e2).
    *)

Definition no_fem (t:iota) := forall e, In e t -> e <> Fem.

Inductive rewrites : iota -> blueExp -> blueExp -> Prop :=
(* (e1 + e2) e ≡ (e1 e) + (e2 e) *)
| R_App_Plus_L : forall t e1 e2 e,
    rewrites t (HApp (HPlus e1 e2) e)
             (HPlus (HApp e1 e) (HApp e2 e))

(* e (e1 + e2) ≡ (e e1) + (e e2) *)
| R_App_Plus_R : forall t e1 e2 e,
    rewrites t (HApp e (HPlus e1 e2))
             (HPlus (HApp e e1) (HApp e e2))

(* (e1 + e2) ⊗ e ≡ e1 ⊗ e + e2 ⊗ e *)
| R_Tensor_Plus_L : forall t e1 e2 e,
    rewrites t (HTensor (HPlus e1 e2) e)
             (HPlus (HTensor e1 e) (HTensor e2 e))

(* e ⊗ (e1 + e2) ≡ e ⊗ e1 + e ⊗ e2 *)
| R_Tensor_Plus_R : forall t e1 e2 e,
    rewrites t (HTensor e (HPlus e1 e2))
             (HPlus (HTensor e e1) (HTensor e e2))

(* (e1 + e2)+ ≡ e1+ + e2+ *)
| R_Dag_Plus : forall t e1 e2,
    rewrites t (HDag (HPlus e1 e2))
             (HPlus (HDag e1) (HDag e2))

(* (e1 ⊗ e2)+ ≡ e1+ ⊗ e2+ *)
| R_Dag_Tensor : forall t e1 e2,
    rewrites t (HDag (HTensor e1 e2))
             (HTensor (HDag e1) (HDag e2))

(* (e1 e2)† ≡ e2† e1† *)
| R_Dag_App : forall t e1 e2,
    rewrites t (HDag (HApp e1 e2))
             (HApp (HDag e2) (HDag e1))

(* (e+)+ ≡ e *)
| R_Double_Dag : forall t e,
    rewrites t (HDag (HDag e)) e

| R_ten: forall t e1 e2 e3 e4, no_fem t -> rewrites t (HApp (HTensor e1 e2) (HTensor e3 e4)) (HTensor (HApp e1 e3) (HApp e2 e4))

| R_dag_id : forall t, rewrites t (HDag HId) HId

| R_app_id_l : forall t e, rewrites t (HApp HId e) e

| R_app_id_r : forall t e, rewrites t (HApp e HId) e.


(* To allow multi-step rewrite *)
Inductive rewrites_recur :  iota -> blueExp -> blueExp -> Prop :=
| RS_Refl : forall t e, rewrites_recur t e e
| RS_Step : forall t e1 e2 e3,
    rewrites t e1 e2 ->
    rewrites_recur t e2 e3 ->
    rewrites_recur t e1 e3.
   
    
(* helper func for T-APP 
Definition uni_tp (zt1 zt2 : xi) : xi :=
    match  zt1, zt2 with
    | p, _ => p
    | _, p => p
    | _, _ => h
    end.


Definition uni_tp (zt1 zt2 : typeflag) : typeflag :=
    match  zt1, zt2 with
    | P, _ => P
    | _, P => P
    | _, _ => H
    end.
*)
(* Typing rules *)
Inductive typing : iota -> blueExp -> tauType -> Prop :=
| T_opF : typing ([Fem]) HAnni (P,[Fem])
| T_opB : forall m,
    typing ([Bos m]) HAnni (P,([Bos m]))
| T_ID : forall t, typing t HAnni (P,t)
| T_DAG : forall t e tp,
    typing t e tp ->
    typing t (HDag e) tp

| T_HER : forall t e e',
    rewrites_recur t e e' ->
    typing t e' (P,t) ->
    typing t e (H,t)

| T_TENSOR : forall  t1 t2 e e' zeta,
    typing t1 e (zeta, t1) ->
    typing t2 e' (zeta, t2) ->
    typing (t1++t2) (HTensor e e') (zeta, (t1++t2))

| T_PLUS : forall t e e' zeta,
    typing t e (zeta, t) ->
    typing t e' (zeta, t) ->
    typing t (HPlus e e') (zeta, t)

| T_App : forall t e e' zeta,
    typing t e (zeta, t) ->
    typing t e' (zeta, t) ->
    typing t (HApp e e') (zeta, t).


(* Check if expression e is canonical *)
Fixpoint canonical_next (e:blueExp) : bool :=
  match e with HTensor e1 e2 => (canonical_next e1) && (canonical_next e2)
             | HApp e1 e2 => (canonical_next e1) && (canonical_next e2)
             | HAnni => true
  | HDag e' =>
      match e' with
      | HAnni => true
      | _ => false
      end

  | HId => true

  | _ => false
  end.

 Fixpoint is_canonical (e : blueExp) : bool :=
  match e with
  | HPlus e1 e2 =>
      is_canonical e1 && is_canonical e2

  | _ => canonical_next e
  end.


Lemma put_get_cus_eq :
   forall f x n, nor_modes f x n -> (put_cus f x (get_cus n f x) n) = f.
Proof.
  intros.
  unfold put_cus,get_cus,put_cu.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  subst.
  unfold nor_modes in H.
  specialize (H n0 H1) as eq1. unfold nor_mode in eq1.
  destruct (f (x,n0)). easy. inv eq1. 
  easy. easy.
Qed.

Lemma get_cus_put_eq :
   forall f x v n, v < 2^n -> nor_modes f x n -> get_cus n (put_cus f x (nat2fb v) n) x = (nat2fb v).
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n).
  simpl.
  unfold nor_modes in H.
  assert (nor_mode (put_cus f x (nat2fb v) n) (x, x0)).
  apply nor_mode_cus_eq. apply H0. easy.
  unfold nor_mode in H2.
  destruct (put_cus f x ((nat2fb v)) n (x, x0)) eqn:eq2.
  unfold put_cus in eq2. simpl in eq2.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu in eq2.
  assert (nor_mode f (x,x0)).
  apply H0. easy.
  unfold nor_mode in H5.
  destruct (f (x, x0)). inv eq2. easy. inv H5. lia. lia.
  inv H2.
  unfold allfalse.
  rewrite nat2fb_bound with (n := n); try easy.
Qed.

Lemma put_cus_same : forall f x g n, nor_modes f x n 
               -> get_cus n f x = g -> put_cus f x g n = f.
Proof.
  intros.
  rewrite <- H0. 
  rewrite put_get_cus_eq. easy. easy.
Qed.

Lemma get_cus_put_neq :
   forall f x y g n, x <> y -> get_cus n (put_cus f x g n) y = get_cus n f y.
Proof.
  intros. unfold get_cus,put_cus.
  apply functional_extensionality. intros.
  simpl.
  bdestruct ( y =? x). lia.
  destruct (f (y, x0)). easy. easy. 
Qed.

Lemma get_put_cus_cut_n : forall n f x g, nor_modes f x n
             -> (get_cus n (put_cus f x g n) x) = cut_n g n.
Proof.
  intros. unfold get_cus,put_cus,cut_n.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n). simpl.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu.
  unfold nor_modes in H0.
  specialize (H x0 H2). unfold nor_mode in H.
  destruct (f (x,x0)). easy. lia. lia.
  lia. easy.
Qed.

Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | _ => None
    end.

Lemma put_get_cu : forall f x, nor_mode f x -> put_cu (f x) (get_cua (f x)) = f x.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H. destruct (f x); inv H.
 reflexivity.
Qed.

Lemma get_put_cu : forall f x v, nor_mode f x -> get_cua (put_cu (f x) v) = v.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H. destruct (f x); inv H.
 reflexivity.
Qed.

Lemma get_cua_t : forall b r, get_cua (nval b r) = b.
Proof.
 intros. unfold get_cua. reflexivity.
Qed.

(* Proofs of types and syntax. *)
Ltac nor_sym := try (apply neq_sym; assumption) ; try assumption.


Lemma iner_neq : forall (x y:var) (a b:nat), x <> y -> (x,a) <> (y,b).
Proof.
  intros. intros R.
  inv R. contradiction.
Qed.

Lemma iner_neq_1 : forall (x:var) (c:posi) a, x <> fst c -> (x,a) <> c.
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Lemma iner_neq_2 : forall (x:var) (c:posi) a, x <> fst c -> c <> (x,a).
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Ltac tuple_eq := intros R; inv R; lia.

Ltac iner_p := try nor_sym; try tuple_eq ; try (apply iner_neq ; assumption)
           ; try (apply iner_neq_1 ; assumption) ; try (apply iner_neq_2 ; assumption).

Lemma exp_neu_t_prop : forall p x l l', exp_neu_l x l p l' -> exp_neu_prop l -> exp_neu_prop l'.
Proof.
 induction p; intros; try easy.
 1-7:inv H; easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Rs :: s :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in H5. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls in *. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Ls :: s :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (length (s :: l'))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Re :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 1-2:inv H; easy.
 inv H.
 apply IHp2 with (x := x) (l := l'0); try easy. 
 apply IHp1 with (x:=x) (l := l); try easy.
Qed.

Lemma dag_canonical : forall e1 t, exists e2, rewrites_recur t e1 e2 /\ is_canonical e2 = true.
Proof.
 induction e1; intros; simpl in *.
  specialize (H0 ([], [p0], [])). simpl in *.
  assert ((nil:(list posi), [p0], nil:(list posi)) = (nil, [p0], nil) \/ In (nil, [p0], nil) T).
  left. easy. apply H0 in H1.
  destruct H1. destruct H2.
  specialize (H2 p0). simpl in *.
  assert (p0 = p0 \/ False). left ; easy.
  apply H2 in H4. destruct H4. rewrite H4.
  destruct x. rewrite update_index_eq.
  exists ((angle_sub (pi32 rmax) r rmax)). easy.
  rewrite update_index_eq.
  exists r. easy.
  easy.
  split.
  destruct (phi p). destruct b.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  split.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite update_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  unfold type_no_change_eta in *.
  intros.
  assert (p <> s).
  unfold flat_union,rec_union in *. simpl in *.
  replace ([p]) with (p :: [] ++ []) in H1 by easy.
  rewrite ford_left_head in H1. simpl in *.
  apply not_or_and  in H1. destruct H1.
  intros R. subst. easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq; easy.
  rewrite update_index_neq; easy.
  rewrite update_index_neq; easy.
  split. 
  intros. inv H2.
  assert (In p (rot s)). rewrite H0. simpl;left;easy.
  apply disjoint_not_rot_had with (T := T) in H2 as G1; try easy.
  apply disjoint_not_rot_nor with (T := T) in H2 as G2; try easy.
  intros.
  apply In_conv with (q' := p) in H3 as G3; try easy.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  unfold ry_rotate in *.
  destruct (phi p). destruct b.
  rewrite update_index_neq.
  apply X1. easy. intros R. subst. easy.
  rewrite update_index_neq.
  apply X1. easy. intros R. subst. easy.
  rewrite update_index_neq.
  apply X1. easy. intros R. subst. easy.
  split.
  intros.
  apply In_conv with (q' := p) in H3 as G3; try easy.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  unfold ry_rotate in *.
  destruct (phi p). destruct b.
  rewrite update_index_neq.
  apply X2. easy. intros R. subst. easy.
  rewrite update_index_neq.
  apply X2. easy. intros R. subst. easy.
  rewrite update_index_neq.
  apply X2. easy. intros R. subst. easy.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  apply X3 in H3. destruct H3.
  destruct (phi p). destruct b.
  bdestruct (posi_eq p p0). subst.
  rewrite update_index_eq.
  exists (angle_sub (pi32 rmax) r rmax). easy.
  rewrite update_index_neq.
  exists x. easy. easy.
  bdestruct (posi_eq p p0). subst.
  rewrite update_index_eq.
  exists r. easy.
  rewrite update_index_neq.
  exists x. easy. easy.
  bdestruct (posi_eq p p0). subst.
  rewrite update_index_eq.
  exists (angle_sum n r rmax). easy.
  rewrite update_index_neq.
  exists x. easy. easy.
  assert (In p (rot th)). rewrite H0. left; easy.
  apply rottoDIn in H2 as G1.
  apply disjoint_not_in with (s' := s) (T := T) in G1 as G2; try easy.
  assert (In s (th :: T)) as G3.
  right; easy.
  specialize (H1 s G3).
  destruct H1 as [X1 [X2 X3]].
  unfold nor_consist_eta, ry_rotate in *. split.
  intros.
  apply X1 in H1 as X4. destruct X4.
  apply hadtoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  split.
  intros.
  apply X2 in H1 as X4. destruct X4.
  apply nortoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  intros.
  apply X3 in H1 as X4. destruct X4.
  apply rottoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite update_index_neq.
  exists x. easy. intros R. subst. easy.
  assert (p <> s).
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H2.
  unfold rec_union in *.
  rewrite H0 in H2. simpl in *.
  apply not_in_app in H2. destruct H2.
  apply not_in_app in H2. destruct H2. apply not_in_app in H4. destruct H4.
  simpl in *. apply not_or_and in H5. destruct H5. easy.
  destruct (phi p). destruct b.
  rewrite update_index_neq; easy.
  rewrite update_index_neq; easy.
  rewrite update_index_neq; easy.
  specialize (mu_handling_preserve rmax qs mu th T phi H H2 H1) as G1. easy.
  unfold nor, nor_sub,had in *. destruct th. destruct p. simpl in *. subst.
  assert (disjoint_record ((l0, qs, l) :: T)).
  clear H1 H2 IHityping.
  unfold disjoint_record in *. 
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in *.
  remember (fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b) T []) as Q.
  clear HeqQ.
  unfold rec_union,nor,had in *; simpl in *.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite app_comm_cons in H.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite disjoint_move in H.
  rewrite <- app_comm_cons in H.
  inv H.
  rewrite disjoint_move in H3.
  rewrite <- app_assoc with (n := Q).
  rewrite <- app_assoc with (n := Q). easy.
  assert (type_consist_eta ((l0, qs, l) :: T) phi).
  clear H0 IHityping H1.
  intros. simpl in *. destruct H0. subst.
  assert ((l0, q :: qs, l) = (l0, q :: qs, l) \/ In (l0, q :: qs, l) T).
  left. easy.
  apply H2 in H0. destruct H0 as [X1 [X2 X3]].
  split. intros.
  apply X1. easy.
  split. intros. apply X2. simpl. right. easy.
  apply X3.
  assert ((l0, q :: qs, l) = s \/ In s T). right. easy.
  apply H2 in H1. destruct H1 as [X1 [X2 X3]].
  easy.
  destruct (IHityping H0 phi H3) as [G1 G2].
  split.
  assert (~ In q (flat_union ((l0, qs, l) :: T))).
  simpl in *.
  clear IHityping H1 H3 G1 G2.
  unfold disjoint_record in H.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H. rewrite fold_left_head_1.
  unfold rec_union,had,nor in *. simpl in *.
  remember (fold_left
         (fun (a0 : list posi) (b : qrecord) =>
          a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q. clear HeqQ.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite app_comm_cons in H.
  rewrite <- app_assoc in H.
  rewrite disjoint_move in H.
  rewrite <- app_comm_cons in H.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  inv H.
  apply not_in_app in H4. destruct H4.
  apply not_in_app in H1. destruct H1.
  intros R.
  apply in_app_or in R. destruct R; try easy.
  apply in_app_or in H4. destruct H4; try easy.
  destruct (phi q). destruct b.
  intros. simpl in *. destruct H5. subst.
  assert ((l0, qs, l) = (l0, qs, l) \/ In (l0, qs, l) T).
  left. easy.
  apply G1 in H5. destruct H5 as [X1 [X2 X3]]. simpl in *.
  split. intros.
  apply X1. easy.
  split. intros. destruct H5. subst. apply G2 in H4. rewrite H4.
  assert ((l0, p :: qs, l) = (l0, p :: qs, l) \/ In (l0, p :: qs, l) T).
  left. easy. apply H2 in H5. destruct H5 as [X4 [X5 X6]].
  apply X5. simpl in *. left. easy.
  apply X2. simpl. easy.
  apply X3.
  assert ((l0, qs, l) = s \/ In s T). right. easy.
  apply G1 in H6. destruct H6 as [X1 [X2 X3]].
  easy. easy. easy.
  destruct (phi q). destruct b.
  intros. apply G2.
  clear H0 H H2 IHityping H1 H3 G1 G2.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H4. rewrite fold_left_head_1.
  clear HeqQ.
  apply not_in_app in H4. destruct H4. apply not_in_app in H.
  destruct H. simpl in *.
  intros R.
  apply in_app_or in R.
  destruct R; try easy.
  apply in_app_or in H2.
  destruct H2; try easy.
  apply not_or_and in H1. destruct H1. easy.
  destruct th. destruct p. simpl in *. subst.
  assert (disjoint_record ((qs, l1, l) :: T)).
  clear H1 H2 IHityping.
  unfold disjoint_record in *. 
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in *.
  remember (fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b) T []) as Q.
  clear HeqQ.
  unfold rec_union,nor,had in *; simpl in *.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite <- app_assoc with (n := Q) in H.
  inv H.
  rewrite <- app_assoc with (n := Q).
  rewrite <- app_assoc with (n := Q). easy.
  assert (type_consist_eta ((qs, l1, l) :: T) phi).
  clear H IHityping H1.
  intros. simpl in *. destruct H. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((q :: qs, l1, l) = (q :: qs, l1, l) \/ In (q :: qs, l1, l) T).
  left. easy.
  apply H2 in H. destruct H as [X1 [X2 X3]].
  split. intros.
  apply X1. simpl in *. right. easy.
  split. intros. apply X2. simpl. easy.
  apply X3.
  assert ((q :: qs, l1, l) = s \/ In s T). right. easy.
  apply H2 in H1. destruct H1 as [X1 [X2 X3]].
  easy.
  destruct (IHityping H0 phi H3) as [G1 G2].
  split.
  assert (~ In q (flat_union ((qs, l1, l) :: T))).
  simpl in *.
  clear IHityping H1 H3 G1 G2.
  unfold disjoint_record in H.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H. rewrite fold_left_head_1.
  unfold rec_union,had,nor in *. simpl in *.
  remember (fold_left
            (fun (a0 : list posi) (b : qrecord) =>
             a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q. clear HeqQ.
  inv H. easy.
  destruct (phi q). destruct b.
  intros. simpl in *. destruct H5. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((qs, l1, l) = (qs, l1, l) \/ In (qs, l1, l) T).
  left. easy.
  apply G1 in H5. destruct H5 as [X1 [X2 X3]]. simpl in *.
  split. intros.
  destruct H5. subst. apply G2 in H4. rewrite H4.
  assert ((p :: qs, l1, l) = (p :: qs, l1, l) \/ In (p :: qs, l1, l) T).
  left. easy. apply H2 in H5. destruct H5 as [X4 [X5 X6]].
  apply X4. simpl in *. left. easy.
  apply X1. easy.
  split. intros.
  apply X2. simpl. easy.
  apply X3.
  assert ((qs, l1, l) = s \/ In s T). right. easy.
  apply G1 in H6. destruct H6 as [X1 [X2 X3]].
  easy. easy. easy.
  destruct (phi q). destruct b.
  unfold type_no_change_eta in *.
  intros. apply G2.
  clear H0 H H2 IHityping H1 H3 G1 G2.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H4. rewrite fold_left_head_1.
  unfold rec_union,nor,had in *. simpl in *.
  remember (fold_left
          (fun (a0 : list posi) (b : qrecord) =>
           a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q.
  clear HeqQ.
  apply not_or_and in H4. destruct H4. easy.
  unfold type_no_change_eta in *. intros. easy.
  unfold type_no_change_eta in *. intros. easy.
  apply disjoint_itype in H1_ as G1; try easy.
  destruct (IHityping1 H phi H0) as [X1 X2].
  destruct (IHityping2 G1 (instr_sem rmax qa phi) X1) as [X3 X4].
  split. easy.
  unfold type_no_change_eta in *.
  intros. rewrite X4; try easy.
  rewrite X2. easy.
  apply ityping_not_in with (s := s) in H1_0; try easy.
Qed.

