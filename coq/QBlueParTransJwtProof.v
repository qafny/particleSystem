
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueSemanticsProof.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueType.

From SQIR Require Import SQIR.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Lia.



(* Particle Transformation *)

Lemma in_state_map_iff :
  forall (l:psi) (τ:iota) (e:C * basisKet),
    In e (state_map l τ) <->
    exists x, In x l /\ state_map_basis x τ = e.
Proof.
  intros l τ e. unfold state_map. rewrite in_map_iff. firstorder. 
Qed.

(* Helper lemmas for WFKet_state_map_basis_bin below.
   cnt2bin always produces a list of bits (each < 2) of the requested length. *)
Lemma cnt2bin_length : forall n len, length (cnt2bin n len) = len.
Proof.
  intros n len. revert n.
  induction len as [| len' IH]; intros n.
  - reflexivity.
  - simpl. rewrite app_length, IH. simpl. lia.
Qed.

Lemma cnt2bin_bound : forall n len, Forall (fun d => (d < 2)%nat) (cnt2bin n len).
Proof.
  intros n len. revert n.
  induction len as [| len' IH]; intros n.
  - simpl. constructor.
  - assert (Hm: (n mod 2 < 2)%nat) by (apply Nat.mod_upper_bound; discriminate).
    simpl. apply Forall_app. split.
    + apply IH.
    + constructor.
      * exact Hm.
      * constructor.
Qed.

(* state_type_bin always produces a list of Bos 2 entries, and is idempotent on
   any such list -- in particular on its own output. *)
Lemma state_type_bin_all_bos2 : forall t, Forall (fun ty => ty = Bos 2) (state_type_bin t).
Proof.
  induction t as [| ty t' IH].
  - simpl. constructor.
  - simpl. apply Forall_app. split.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx.
    + apply IH.
Qed.

Lemma state_type_bin_fixpoint : forall t, Forall (fun ty => ty = Bos 2) t -> state_type_bin t = t.
Proof.
  induction t as [| ty t' IH]; intros H.
  - reflexivity.
  - inversion H as [| a l Ha Ht]; subst.
    simpl. rewrite IH; auto.
Qed.

Lemma state_type_bin_idempotent : forall t, state_type_bin (state_type_bin t) = state_type_bin t.
Proof.
  intros t. apply state_type_bin_fixpoint. apply state_type_bin_all_bos2.
Qed.

Lemma all_eq_is_repeat : forall (l : iota) (x : particle),
  Forall (fun ty => ty = x) l -> l = repeat x (length l).
Proof.
  induction l as [| a l' IH]; intros x Hf.
  - reflexivity.
  - simpl. pose proof (Forall_inv Hf) as Ha.
    pose proof (Forall_inv_tail Hf) as Hl.
    simpl in Ha. subst a. f_equal. apply IH. exact Hl.
Qed.

Lemma state_type_bin_eq_repeat : forall t,
  state_type_bin t = repeat (Bos 2) (length (state_type_bin t)).
Proof.
  intros t. apply all_eq_is_repeat. apply state_type_bin_all_bos2.
Qed.

(* state_map_basis_helper's second output is exactly state_type_bin of whatever
   type list it was given; its first output (the flattened bit-ket) is bounded
   and has the matching length. *)
Lemma state_map_basis_helper_snd :
  forall t len input, snd (state_map_basis_helper len input t) = state_type_bin t.
Proof.
  induction t as [| ty t' IH]; intros len input.
  - reflexivity.
  - simpl.
    destruct (state_map_basis_helper len input t') as [ket_app ty_app] eqn:E.
    simpl in *.
    f_equal.
    rewrite <- (IH len input).
    rewrite E. reflexivity.
Qed.

Lemma state_map_basis_helper_fst_bound :
  forall t len input, Forall (fun d => (d < 2)%nat) (fst (state_map_basis_helper len input t)).
Proof.
  induction t as [| ty t' IH]; intros len input.
  - simpl. constructor.
  - simpl.
    pose proof (IH len input) as IH'.
    destruct (state_map_basis_helper len input t') as [ket_app ty_app] eqn:E.
    simpl in IH'. simpl.
    apply Forall_app. split.
    + apply cnt2bin_bound.
    + exact IH'.
Qed.

Lemma state_map_basis_helper_fst_length :
  forall t len input, length (fst (state_map_basis_helper len input t)) = length (state_type_bin t).
Proof.
  induction t as [| ty t' IH]; intros len input.
  - reflexivity.
  - simpl.
    pose proof (IH len input) as IH'.
    destruct (state_map_basis_helper len input t') as [ket_app ty_app] eqn:E.
    simpl in IH'. simpl.
    rewrite app_length, app_length, cnt2bin_length.
    f_equal.
    + rewrite repeat_length. reflexivity.
    + exact IH'.
Qed.

Lemma nleft_nth_cons : forall (a : nat) (l : list nat),
  nleft (fun x => nth x (a :: l) 0%nat) 1 = fun x => nth x l 0%nat.
Proof.
  intros a l. unfold nleft. apply functional_extensionality.
  intros x. rewrite Nat.add_1_r. reflexivity.
Qed.

(* Any bit-list, read back as a nth-indexed ket, is well-formed at the
   all-qubit type of matching length. *)
Lemma WFKet_from_list : forall (l : list nat) (t : iota),
  t = state_type_bin (repeat (Bos 2) (length l)) ->
  Forall (fun d => (d < 2)%nat) l ->
  WFKet t (fun x => nth x l 0%nat).
Proof.
  induction l as [| a l' IH]; intros t Ht Hf.
  - subst t. simpl. constructor.
  - pose proof (Forall_inv Hf) as Ha.
    pose proof (Forall_inv_tail Hf) as Hl.
    assert (Et : t = Bos 2 :: state_type_bin (repeat (Bos 2) (length l'))).
    { rewrite Ht. simpl. reflexivity. }
    rewrite Et.
    apply WFManyB with (m := 2%nat).
    + simpl. exact Ha.
    + rewrite nleft_nth_cons. apply IH; auto.
Qed.

Lemma WFKet_state_map_basis_bin :
  forall (sty : iota) (s : C * basisKet),
    WFKet sty (snd s) ->
    WFKet (state_type_bin sty) (snd (state_map_basis s (state_type_bin sty))).
Proof.
  intros sty s _.
  destruct s as [amp input]. unfold state_map_basis. simpl.
  pose proof (state_map_basis_helper_snd (state_type_bin sty) (length (state_type_bin sty)) input) as Hsnd.
  pose proof (state_map_basis_helper_fst_bound (state_type_bin sty) (length (state_type_bin sty)) input) as Hbound.
  pose proof (state_map_basis_helper_fst_length (state_type_bin sty) (length (state_type_bin sty)) input) as Hlen.
  rewrite state_type_bin_idempotent in Hsnd, Hlen.
  destruct (state_map_basis_helper (length (state_type_bin sty)) input (state_type_bin sty)) as [bin_ket ty_out] eqn:E.
  simpl in *.
  apply WFKet_from_list.
  - rewrite Hlen.
    assert (Hall : Forall (fun ty => ty = Bos 2) (repeat (Bos 2) (length (state_type_bin sty)))).
    { apply Forall_forall. intros y Hy. apply repeat_spec in Hy. exact Hy. }
    rewrite (state_type_bin_fixpoint _ Hall).
    apply state_type_bin_eq_repeat.
  - exact Hbound.
Qed.


(* Sub lemma for proving particle_transoform_correctness.
  Well-form state is kept when transforming from high-level to low-level *)
Lemma WFState_state_map_bin: forall sty s, WFState sty s ->
  WFState (state_type_bin sty) (state_map s (state_type_bin sty)).
Proof.
  intros sty s Hwf e Hin.
  apply in_state_map_iff in Hin.
  destruct Hin as [x [HxIn Heq]].
  subst e.  
  apply WFKet_state_map_basis_bin.
  apply Hwf. easy.
Qed. 
  

(* Theorem for particle transformation from low-level to high-level *)
Theorem particle_transoform_correctness: forall n st_type e op_type s, 
  typing st_type e op_type -> WFState st_type s -> exists s1,
  let H' := bexp_to_lowprog e st_type in
  let s' := state_map s st_type in
  let st_type' := state_type_bin st_type in
  let s1' := state_map s1 st_type' in
  blue_sem n st_type e s s1 /\ WFState st_type' s1' /\ blue_sem_low H' s' s1'.
  intros n st_type e op_type sin Hty Hwf.
  Proof.
    destruct (type_soundness st_type e op_type n sin Hty Hwf)
    as [s1 [Hsem HWFr]].

    exists s1.

    repeat split.

    - exact Hsem.
    
    - (* WFState (state_type_bin st_type) (state_map s1 (state_type_bin st_type)) *)
    (* Any lemma that says mapping/bin-typing preserves WF works here *)
    apply WFState_state_map_bin; exact HWFr.

    
    - admit. 
      (* apply bexp_to_lowprog_sound; exact Hsem. *)

  
Admitted. 


(* Theorem hermitian_high2low: forall (H : highprog) is_hermitian_high H ->
high2low H = L-> wf_lowprog L.
Proof.
Admitted. *)


Lemma WF_pauli2mat : forall p : paulimat, WF_Matrix (pauli2mat p).
Proof.
  intro p; destruct p.
  - show_wf.
  - show_wf.
  - show_wf.
  - apply WF_I.
Qed.

Lemma wf_lowprogten2mat :
  forall (amp : C) (n : nat) (f : nat -> paulimat),
    WF_Matrix (lowprogten2mat amp n f).
Proof.
  intros amp n f.
  induction n as [| n' IH].
  - simpl.
    (* lowprogten2mat amp 0 f = scale amp (I 1) *)
    auto with wf_db. 
  - simpl.
    (* kron (pauli2mat (f n')) (lowprogten2mat amp n' f) *)
    apply WF_kron. 
    -- easy.
    -- easy.
    -- apply WF_pauli2mat.
    -- easy.  
Qed.

Lemma wf_lowprog2mat :
  forall (lp : lowprog) (n : nat),
    WF_Matrix (lowprog2mat lp n).
Proof.
  intros lp n.
  induction lp as [| ten lpx IH].
  - simpl. apply WF_Zero.
  - simpl.
    destruct ten as [[amp k] f].
    unfold Mplus. apply WF_plus.  
    -- apply wf_lowprogten2mat.
    -- easy.
Qed.

  
  



