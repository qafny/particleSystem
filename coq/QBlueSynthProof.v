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

Lemma long_z_WF: forall n f r, WF_Matrix (fst (long_z n f r)).
Proof.
  intros. induction n. simpl in *. 
  auto with wf_db.
  simpl in *.
  destruct (is_i (f n)).
  destruct (long_z n f r). simpl in *.
  auto with wf_db.
  destruct (long_z n f r).
  destruct b. unfold first_pad. 
  bdestruct (n =? 0);subst. restore_dims. simpl in *.
  auto with wf_db.
  bdestruct (n =? 1); subst. restore_dims. simpl in *.
  auto with wf_db.
  restore_dims. simpl in *.
  replace (2 ^ n + (2 ^ n + 0)) with (2^n * 2) by lia.
  apply WF_plus.
  auto with wf_db. auto with wf_db.
  simpl in *. auto with wf_db.
Qed.

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
  unfold first_pad in *.
  replace (3 * PI / 2 + PI / 2)%R with (2 *PI)%R by lra.
  replace (PI / 2 + PI / 2)%R with (PI)%R by lra.
  solve_matrix.
  1-4: autorewrite with R_db C_db Cexp_db trig_db.
  unfold Copp,Cmult,Cplus; simpl in *.
  autorewrite with R_db C_db Cexp_db trig_db.
  repeat rewrite Ropp_mult_distr_l.
  replace (- (-1))%R with 1%R by lra.
  autorewrite with R_db C_db Cexp_db trig_db.
  specialize (sin2_cos2 ((PI * / 2 * / 2))) as H.
  unfold Rsqr in H. rewrite Rplus_comm. rewrite H. lca.
  lca. lca.
  unfold Copp,Cmult,Cplus; simpl in *.
  autorewrite with R_db C_db Cexp_db trig_db.
  rewrite Ropp_mult_distr_r.
  repeat rewrite Ropp_mult_distr_l.
  replace (- (-1))%R with 1%R by lra.
  autorewrite with R_db C_db Cexp_db trig_db.
  specialize (sin2_cos2 ((PI * / 2 * / 2))) as H.
  unfold Rsqr in H. rewrite H. lca.
  rewrite H.
  easy.
  gridify.
  rewrite IHn. easy.
Qed.



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


Fixpoint add_h (n:nat) (f: nat -> paulimat) : Square (2^n) :=
  match n with
   | 0 => I 1
   | S m => if is_i (f m) then add_h m f ⊗ I 2 else add_h m f ⊗ hadamard
  end.

Definition long_x_inter (n:nat) (f: nat -> paulimat) t :=
  add_h n f × (fst (long_z n f t)) × add_h n f.

Fixpoint add_front_in (n:nat) (f: nat -> paulimat) : Square (2^n) :=
  match n with
   | 0 => I 1
   | S m => match (f m) with
              | pauliy => add_front_in m f ⊗ phase_shift (PI / (IZR 2))
              | pauliz => add_front_in m f ⊗
                      (phase_shift (PI / (IZR 2)) × x_rotation (PI / (IZR 2)) × (phase_shift (PI / (IZR 2))))
              | _ => add_front_in m f ⊗ I 2
            end
  end.

Lemma phase_rotation_join : forall a a' b c, phase_shift a × rotation a' b c = rotation a' (b+a) c.
Proof.
  intros. solve_matrix. 
  all: autorewrite with R_db C_db Cexp_db trig_db.
  lca. lca.
Qed.

Lemma rotation_phase_join : forall a a' b c, rotation a' b c × phase_shift a = rotation a' b (a+c).
Proof.
  intros. solve_matrix. 
  all: autorewrite with R_db C_db Cexp_db trig_db.
  lca. lca.
Qed.

Definition inter_in_synth (n:nat) (f: nat -> paulimat) t :=
  (adjoint (add_front_in n f)) × long_x_inter n f t × (add_front_in n f).

Lemma add_front_eq: forall n f, add_h n f × add_front_in n f = add_front n f.
Proof.
  intros. induction n; simpl in *.
  gridify.
  destruct (f n); simpl in *.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn. gridify.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn. easy.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn.
  assert ((hadamard
   × (phase_shift (PI / 2) × x_rotation (PI / 2)
      × phase_shift (PI / 2))) = I 2).
  rewrite <- Rx_rotation.
  rewrite phase_rotation_join.
  rewrite rotation_phase_join.
  rewrite <- hadamard_rotation.
  replace (3 * PI / 2 + PI / 2)%R with (2 *PI)%R by lra.
  replace (PI / 2 + PI / 2)%R with (PI)%R by lra.
  solve_matrix.
  1-4: autorewrite with R_db C_db Cexp_db trig_db.
  unfold Copp,Cmult,Cplus; simpl in *.
  autorewrite with R_db C_db Cexp_db trig_db.
  repeat rewrite Ropp_mult_distr_l.
  replace (- (-1))%R with 1%R by lra.
  autorewrite with R_db C_db Cexp_db trig_db.
  specialize (sin2_cos2 ((PI * / 2 * / 2))) as H.
  unfold Rsqr in H. rewrite Rplus_comm. rewrite H. lca.
  lca. lca.
  unfold Copp,Cmult,Cplus; simpl in *.
  autorewrite with R_db C_db Cexp_db trig_db.
  rewrite Ropp_mult_distr_r.
  repeat rewrite Ropp_mult_distr_l.
  replace (- (-1))%R with 1%R by lra.
  autorewrite with R_db C_db Cexp_db trig_db.
  specialize (sin2_cos2 ((PI * / 2 * / 2))) as H.
  unfold Rsqr in H. rewrite H. lca.
  rewrite H.
  easy.
  gridify.
  rewrite IHn. easy.
Qed.

Lemma add_h_inv_same : forall n f, (add_h n f) † =  add_h n f.
Proof.
  intros. induction n.
  gridify.
  simpl in *.
  destruct (is_i (f n)).
  autorewrite with eval_db.
  restore_dims.
  rewrite kron_adjoint.
  gridify. rewrite IHn. easy.
  restore_dims.
  rewrite kron_adjoint.
  rewrite IHn. autorewrite with eval_db.
  assert ((hadamard) † = hadamard).
  solve_matrix_fast. rewrite H. easy.
Qed.

Lemma synth_in_machine_same: forall n amp f,
                    inter_in_synth n f amp = exp_paulis n amp f.
Proof.
 unfold inter_in_synth,long_x_inter,exp_paulis.
 intros.
 repeat rewrite Mmult_assoc.
 rewrite add_front_eq.
 rewrite <- Mmult_assoc.
 rewrite <- add_h_inv_same.
 rewrite <- Mmult_adjoint.
 rewrite add_front_eq. easy.
Qed.



Definition conj_paulis (a b:paulimat) :=
  match (a,b) with (paulix,paulix) => (C1,paulii)
                 | (pauliy,pauliy) => (C1,paulii)
                 | (pauliz,pauliz) => (C1,paulii)
                 | (paulii,paulii) => (C1,paulii)
                 | (paulix,pauliy) => (Ci,pauliz)
                 | (paulix,pauliz) => (-Ci,pauliy)
                 | (paulix,paulii) => (C1,paulix)
                 | (pauliy,paulix) => (-Ci,pauliz)
                 | (pauliy,pauliz) => (Ci,paulix)
                 | (pauliy,paulii) => (C1,pauliy)
                 | (pauliz,paulix) => (Ci,pauliy)
                 | (pauliz,pauliy) => (-Ci,paulix)
                 | (pauliz,paulii) => (C1,pauliz)
                 | (paulii,paulix) => (C1,paulix)
                 | (paulii,pauliy) => (C1,pauliy)
                 | (paulii,pauliz) => (C1,pauliz)
  end.

Definition inter_pauli (a:paulimat) :=
  match a with paulii => I 2
             | paulix => σx
             | pauliy => σy
             | pauliz => σz
  end.

Lemma conj_correct : forall a b , inter_pauli a × inter_pauli b 
           = (fst (conj_paulis a b)) .* inter_pauli (snd (conj_paulis a b)).
Proof.
  intros. unfold conj_paulis,inter_pauli in *.
  destruct a;simpl in *. destruct b;simpl in *.
  1-4:solve_matrix_fast.
  destruct b;simpl in *.
  1-4:solve_matrix_fast.
  destruct b;simpl in *.
  1-4:solve_matrix_fast.
  destruct b;simpl in *.
  1-4:solve_matrix_fast.
Qed.

