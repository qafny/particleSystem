
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueSemanticsProof.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueType.

From SQIR Require Import SQIR. 



(* Particle Transformation *)

Lemma in_state_map_iff :
  forall (l:psi) (τ:iota) (e:C * basisKet),
    In e (state_map l τ) <->
    exists x, In x l /\ state_map_basis x τ = e.
Proof.
  intros l τ e. unfold state_map. rewrite in_map_iff. firstorder. 
Qed.

Lemma WFKet_state_map_basis_bin :
  forall (sty : iota) (s : C * basisKet),
    WFKet sty (snd s) ->
    WFKet (state_type_bin sty) (snd (state_map_basis s (state_type_bin sty))).
Proof.
  intros sty s IH.
  destruct sty as [| a sty'].
  - simpl in *. unfold state_map_basis. simpl in *.  
Admitted.


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

  
  



