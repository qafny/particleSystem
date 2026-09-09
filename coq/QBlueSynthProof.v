(* Do synthesization upon different hardware *)

Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.


(* Define the synth step for IBM digital computer. *)
From SQIR Require Import ExtractionGateSet.
From VOQC Require Import FullGateSet.
From VOQC Require Import Main.


Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueProofUtility.


Module EG := ExtractionGateSet.
Module FG := FullGateSet.

Fixpoint front_half (n:nat) (f: nat -> paulimat) :=
  match n with
   | 0 => EG.SKIP
   | S m => match (f m) with
              | paulix => EG.useq (front_half m f)  (EG.H m) 
              | pauliy => EG.useq (front_half m f) (EG.useq (EG.U1 (PI / IZR 2) m) (EG.H m))
              | _ => front_half m f
            end
  end.

Fixpoint mid_paulis (n:nat) (amp:R) f :=
  match n with
   | 0 => (EG.SKIP,None)
   | S m => if is_i (f m)
            then mid_paulis m amp f
            else let (c,b') := mid_paulis m amp f in
                 match b' with None => (EG.U1 amp m, Some m)
                            | Some v => (EG.useq (EG.CX m v) (EG.useq c (EG.CX m v)), Some m)
                 end
  end.


Definition synth_digital_ibm_apauli (n:nat) (t:R) (f: nat -> paulimat) :=
 let (c,b') := (mid_paulis n t f) in EG.useq (front_half n f) (EG.useq c (EG.invert (front_half n f))).

Open Scope nat_scope.

Lemma change_dim_unfold: forall (u: EG.ucom EG.U) m n,
  UnitarySem.uc_eval (EG.to_base_ucom m u) 
   = UnitarySem.uc_eval (UnitaryOps.cast ((EG.to_base_ucom n u)) m).
Proof.
  intros u m n.
  rewrite <- change_dim.
  unfold EG.uc_eval. easy.
Qed. 

Lemma front_has_WF: forall n f, well_formed (front_half n f).
Proof.
  intros. induction n. simpl in *.
  apply WF_uapp. easy.
  simpl in *.
  destruct (f n). apply WF_useq. apply IHn.
  apply WF_uapp. easy.
  apply WF_useq. apply IHn.
  apply WF_useq. apply WF_uapp. easy. apply WF_uapp. easy.
  apply IHn. apply IHn.
Qed.

Lemma front_half_WF : forall n f, 0 < n -> uc_well_typed (to_base_ucom n (front_half n f)).
Proof.
  intros.
  induction n; simpl in *. inv H.
  destruct n. destruct (f 0); simpl in *.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  apply SQIR.WT_seq. apply SQIR.WT_app1. lia.
  apply uc_well_typed_H. lia.
  apply SQIR.WT_seq. apply SQIR.WT_app1. lia.
  apply SQIR.WT_seq. apply SQIR.WT_app1. lia.
  apply uc_well_typed_H. lia.
  apply SQIR.WT_app1. lia.
  apply SQIR.WT_app1. lia.
  remember (S n) as a.
  destruct (f a); simpl in *.
  apply SQIR.WT_seq.
  apply change_dim_WT with (m := a); try lia.
  apply front_has_WF. apply IHn.
  lia.
  apply uc_well_typed_H.
  lia.
  apply SQIR.WT_seq.
  apply change_dim_WT with (m := a); try lia.
  apply front_has_WF. apply IHn. lia.
  apply SQIR.WT_seq. apply SQIR.WT_app1. lia.
  apply uc_well_typed_H. lia.
  apply change_dim_WT with (m := a); try lia.
  apply front_has_WF. apply IHn. lia.
  apply change_dim_WT with (m := a); try lia.
  apply front_has_WF. apply IHn. lia.
Qed.

Lemma synth_front_correctness: forall n f, 0 < n -> add_front n f = EG.uc_eval n (front_half n f).
Proof.
  intros.
  induction n; simpl in *. inv H.
  destruct n; simpl in *.
  unfold EG.uc_eval. 
  destruct (f 0); simpl in *.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  rewrite eval_H. autorewrite with eval_db.
  bdestruct (0 + 1 <=? 1).
  rewrite I_rotation. gridify. inv H0.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  autorewrite with eval_db.
  bdestruct (0 + 1 <=? 1).
  rewrite I_rotation. rewrite phase_shift_rotation.
  gridify. inv H0.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  rewrite I_rotation. autorewrite with eval_db.
  bdestruct (0 + 1 <=? 1). gridify. inv H0.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  rewrite I_rotation. autorewrite with eval_db.
  bdestruct (0 + 1 <=? 1). gridify. inv H0.
  rewrite IHn; try lia.
  destruct (f (S n)); simpl in *.
  unfold EG.uc_eval. 
  simpl in *.
  rewrite denote_H.
  rewrite change_dim_unfold with (m := S (S n)) (n := S n).
  replace (S (S n)) with (S n + 1) by lia.
  rewrite <- pad_dims_r.
  repeat rewrite kron_1_r.
  repeat rewrite kron_1_l; try auto_wf.
  autorewrite with eval_db.
  replace (S n + 1) with (S (S n)) by lia.
  bdestruct (S (S n) <=? S (S n)).
  assert ((S (S n) - S (S n)) = 0) by lia.
  rewrite H1. gridify. easy. lia.
  assert (uc_well_typed (to_base_ucom (S n) (front_half (S n) f))) as WF.
  apply front_half_WF. lia.
  simpl in *. apply WF.
  unfold EG.uc_eval. 
  simpl in *.
  rewrite denote_H.
  rewrite change_dim_unfold with (m := S (S n)) (n := S n).
  replace (S (S n)) with (S n + 1) by lia.
  rewrite <- pad_dims_r.
  repeat rewrite kron_1_r.
  repeat rewrite kron_1_l; try auto_wf.
  autorewrite with eval_db.
  replace (S n + 1) with (S (S n)) by lia.
  bdestruct (S (S n) <=? S (S n)).
  assert ((S (S n) - S (S n)) = 0) by lia.
  rewrite H1. simpl in *. rewrite phase_shift_rotation. gridify. easy.
  assert (x = S n) by lia. subst.
  restore_dims.
  apply WF_uc_eval. lia.
  assert (uc_well_typed (to_base_ucom (S n) (front_half (S n) f))) as WF.
  apply front_half_WF. lia.
  simpl in *. apply WF. simpl in *.
  unfold EG.uc_eval. 
  simpl in *.
  rewrite change_dim_unfold with (m := S (S n)) (n := S n).
  replace (S (S n)) with (S n + 1) by lia.
  rewrite <- pad_dims_r. easy.
  assert (uc_well_typed (to_base_ucom (S n) (front_half (S n) f))) as WF.
  apply front_half_WF. lia.
  simpl in *. apply WF.
  unfold EG.uc_eval. 
  simpl in *.
  rewrite change_dim_unfold with (m := S (S n)) (n := S n).
  replace (S (S n)) with (S n + 1) by lia.
  rewrite <- pad_dims_r. easy.
  assert (uc_well_typed (to_base_ucom (S n) (front_half (S n) f))) as WF.
  apply front_half_WF. lia.
  simpl in *. apply WF.
Qed.

Lemma mid_paulis_WF: forall a amp f, uc_well_typed (EG.to_base_ucom a (fst (mid_paulis a amp f))).
Proof.
Admitted.

Lemma long_z_WF: forall n f r, WF_Matrix (fst (long_z n f r)).
Proof.
Admitted.

Definition good_b (v: option nat) (b:bool) := match v with None => b = false | Some a => b = true end.

Lemma synth_digital_mid_same: forall n dim amp f, n <= dim -> 0 < dim ->
                    EG.uc_eval dim (fst (mid_paulis n amp f)) = (fst (long_z n f amp)) ⊗ I (2^(dim - n))
                            /\ good_b (snd (mid_paulis n amp f)) (snd (long_z n f amp)).
Proof.
  intros.
  induction n; simpl in *; try lia.
  split.
  unfold EG.uc_eval.
  autorewrite with eval_db; try lia. gridify. easy. easy.
  destruct (is_i (f n)); unfold EG.uc_eval in *; simpl in *.
  destruct (long_z n f amp) eqn:eq1.
  destruct (mid_paulis n amp f) eqn:eq2.
  simpl in *.
  destruct IHn;try lia.
  split. rewrite H1. restore_dims.
  rewrite kron_assoc. rewrite id_kron.
  assert (2 ^ (dim - n) = 2 ^ 1 * 2 ^ (dim - S n)).
  rewrite <- Nat.pow_add_r.
  replace (1 + (dim - S n)) with (dim - n) by lia. easy.
  rewrite H3. simpl in *. easy.
  replace m with (fst (long_z n f amp)).
  apply long_z_WF. rewrite eq1. easy.
  auto_wf. auto_wf.
  easy.
  destruct (mid_paulis n amp f) eqn:eq1.
  destruct (long_z n f amp) eqn:eq2.
  simpl in *.
  destruct IHn. lia. split.
  unfold good_b in *. destruct o. subst. simpl in *.
  rewrite H1.
  rewrite denote_cnot.
  rewrite unfold_ueval_cnot.
  bdestruct (n <? n0).
  autorewrite with eval_db; try lia.
  bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim). simpl in *.
  replace ((dim - (n + S (n0 - n - 1 + 1)))) with (dim - S n0) by lia.
  simpl in *. 
Admitted.

(*

  gridify.
  prep_matrix_equality.
  rewrite kron_plus_distr_l.
  rewrite Mmult_assoc; try auto_wf.
  rewrite kron_plus_distr_r.
  Set Printing All.
  rewrite kron_id_dist_l.
  bdestruct (0 + 1 <=? 1); try lia.
  replace R0 with (IZR Z0); try (easy; simpl in.
  split.
  rewrite I_rotation. gridify. easy.
  rewrite phase_shift_rotation. split.
  autorewrite with eval_db.
  bdestruct (0 + 1 <=? 1);try lia.
  gridify. easy.
  remember (S n) as a.
  destruct (is_i (f a)).
  destruct (long_z a f amp). simpl in *.
  assert (0 < a) by lia. apply IHn in H0. destruct H0.
  rewrite <- H0; try lia. split.
  unfold EG.uc_eval.
  rewrite change_dim_unfold with (m := S a) (n := a).
  replace (S a) with (a + 1) by lia.
  rewrite <- pad_dims_r. easy.
  apply mid_paulis_WF. easy.
  destruct (mid_paulis a amp f) eqn:eq1; simpl in *.
  destruct (long_z a f amp) eqn:eq2. simpl in *.
  destruct o. simpl in *. destruct IHn;subst;simpl in *. lia.


Lemma mid_paulis_WF : forall n amp f b j, well_formed ((mid_paulis n amp f b j)).
Proof.
  induction n; intros; simpl in *.
  apply WF_uapp. easy.
  destruct (is_i (f n) || (j =? 0)). apply IHn.
  bdestruct (j =? 1).
  destruct b.
  apply WF_useq.
  apply WF_uapp. easy.
  apply WF_useq.
  apply WF_uapp. easy.
  apply WF_uapp. easy.
  apply WF_uapp. easy.
  destruct b.
  apply WF_useq.
  apply WF_uapp. easy.
  apply WF_useq. apply IHn.
  apply WF_uapp. easy.
  apply IHn.
Qed.



Lemma mid_paulis_aux_EG_WF : forall n dim amp f b j, n <= dim -> 0 < dim -> good_b n dim b ->
                   uc_well_typed (to_base_ucom dim (mid_paulis n amp f b j)).
Proof.
  induction n; intros; simpl in *. apply SQIR.WT_app1. easy.
  destruct (is_i (f n) || (j =? 0)); simpl in *.
  apply IHn; try lia.
  unfold good_b in *. destruct b; try easy. split. lia. lia.
  bdestruct (j =? 1). simpl.
  destruct b. simpl.
  apply SQIR.WT_seq. apply uc_well_typed_CNOT. unfold good_b in *.
  split. lia. split. lia. lia.
  apply SQIR.WT_seq.
  apply SQIR.WT_app1. lia.
  apply uc_well_typed_CNOT.
  unfold good_b in *. split. lia.
  split. lia. lia.
  simpl.
  apply SQIR.WT_app1. lia.
  unfold good_b in *. destruct b.
  simpl. constructor.
  apply uc_well_typed_CNOT.
  split. lia. split. lia. lia.
  simpl. constructor.
  apply IHn; try lia.
  apply uc_well_typed_CNOT.
  split. lia. split. lia. lia.
  apply IHn. lia. lia. split. lia. easy.
Qed.


Lemma long_z_wf: forall n f j amp, WF_Matrix (long_z n f j amp).
Proof.
  induction n; intros; try auto_wf. simpl.
  destruct (is_i (f n) || (j =? 0)). simpl. apply WF_kron; try lia. apply IHn.
  auto_wf.
  bdestruct (j =? 1). apply WF_kron; try lia. apply IHn. auto_wf.
  restore_dims.
  apply WF_plus.
  apply WF_kron; try lia. apply IHn. auto_wf.
  apply WF_kron; try lia. apply IHn. auto_wf.  
Qed.
 *)


Theorem synth_digital_ibm_pauli_correctness: forall (n : nat) (t : R) (f : nat->paulimat), 0 < n ->
  exp_paulis n t f = EG.uc_eval n (synth_digital_ibm_apauli n t f).
Proof.
  intros.
  unfold exp_paulis,synth_digital_ibm_apauli.
  destruct (long_z n f t ) eqn:eq1.
  destruct (mid_paulis n t f) eqn:eq2.
  rewrite synth_front_correctness; try lia.
  specialize (synth_digital_mid_same n n t f) as H1.
  destruct H1; try lia; simpl in *.
  assert (fst (long_z n f t) ⊗ I (2 ^ (n - n)) = fst (long_z n f t)).
  replace (n-n) with 0 by lia. simpl in *.
  rewrite kron_1_r. easy. rewrite H2 in H0.
  rewrite eq1 in H0; simpl in *. rewrite <- H0.
  rewrite eq2.
  unfold EG.uc_eval; simpl in *.
  specialize (invert_same n (front_half n f)) as H3.
  unfold EG.uc_eval in H3.
  rewrite H3.
  simpl in *.
  rewrite <- invert_correct.
  easy.
  apply front_has_WF. 
Qed.




(* U† A U *)
Definition conj {n} (U A : Matrix n n) : Matrix n n :=
  Mmult (U†) (Mmult A U).


Fixpoint prod {n : nat} (us : list (Matrix n n)) : Matrix n n :=
  match us with
  | [] => I n
  | u :: tl => (prod tl) × u   (* gives U_n ... U_1 if list is [U1;...;Un] *)
  end.

(*
Lemma big_conj_goal: forall {n:nat} (us : list (Matrix n n)) (P : Matrix n n),
  (prod us)† × P × (prod us) = P'. *)


Lemma conj_mul {n} (A B P : Matrix n n) :
  ((A × B)†) × P × (A × B)
  = (B†) × ((A†) × P × A) × B.
Proof.
  (* typical steps: expand dagger of product, reassociate *)
  rewrite Mmult_adjoint.         (* (A×B)† = B† × A† *)
  repeat rewrite Mmult_assoc.  (* reassociate × *)
  reflexivity.
Qed.


Lemma conj_prod {n} (us : list (Matrix n n)) (P : Matrix n n) :
  (prod us)† × P × (prod us)
  = fold_left (fun acc u => conj u acc) us P.
Proof.
Admitted.
(*
  induction us as [|u tl IH].
  - simpl. (* prod [] = I; fold_left ... [] P = P *)
    (* rewrite with dagger_I, I_mult, mult_I, etc. *)
    (* goal becomes P = P *)
    now simp_matrix.  (* or your library’s simp tactic *)
  - simpl.
    (* prod (u::tl) = prod tl × u *)
    (* Use conj_mul with A := prod tl, B := u *)
    rewrite conj_mul.
    (* reduce using IH *)
    rewrite IH.
    (* fold_left unfolding *)
    simpl.
    (* then reassociate as needed *)
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed. *)

Definition conj_by_list (us : list U) (P : Pauli) : Pauli :=
  fold_left (fun acc u => conj u acc) us P.

(* Theorem conj_prod_computes (us : list U) (P : Pauli) :
  (prod us)† × P × (prod us) = conj_by_list us P.
Proof.
  rewrite conj_prod.
  (* goal: fold_left (fun acc u => conj u acc) us P = conj_by_list us P *)
  reflexivity.
Qed. *)


Lemma conj_prod_computes :
  forall us P,
    denote_Pauli (conj_by_list us P)
    = (denote_U (prod us))† × denote_Pauli P × denote_U (prod us).
Proof.
  induction us as [|u us IH]; intros P.
  - (* us = [] *)
    cbv [conj_by_list prod]; cbn.
    (* goal becomes denote_Pauli P = I† × denote_Pauli P × I *)
    (* finish with matrix identity lemmas *)
    simp_matrix.  (* or: rewrite Mmult_1_l, Mmult_1_r, dagger_I, etc. *)
  - (* us = u :: us *)
    cbv [conj_by_list]; cbn.
    (* fold_left over (u :: us) reduces to fold_left over us with initial conj u P *)
    (* LHS: denote_Pauli (conj_by_list us (conj u P)) *)
    rewrite IH.
    (* Now use conj_sound to replace denote_Pauli (conj u P) with U† P U *)
    rewrite conj_sound.
    (* Now rearrange products to match (prod (u::us))† P (prod (u::us)) *)
    (* You also need a lemma relating denote_U (prod (u::us)) to denote_U u × denote_U (prod us) *)
    (* and dagger of a product: (AB)† = B† A† *)
    simp_matrix.  (* or explicit associativity rewrites *)
Qed.



Lemma conj_H_X : conj H X = Z.  (* i.e., H† X H = Z; since H†=H *)
Lemma conj_H_Z : conj H Z = X.
Lemma conj_H_Y : conj H Y = - Y.

Lemma conj_S_X : conj S X = Y.      (* depending on your convention; may be -Y *)
Lemma conj_S_Y : conj S Y = - X.
Lemma conj_S_Z : conj S Z = Z.


Goal (prod us)† × P × (prod us) = P'.
Proof.
  rewrite conj_prod.
  (* now goal is fold_left (fun acc u => conj u acc) us P = P' *)
  (* if us is concrete, simp + rewrite using the conj_* lemmas *)
  repeat (cbn; try rewrite conj_H_X; try rewrite conj_H_Z; try rewrite conj_S_X; ...).
  reflexivity.
Qed.

