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

(* Define long z interaction as the basis for exp of a pauli-string matrix. *)
Fixpoint count_paulis (n:nat) (f:nat -> paulimat) : nat :=
  match n with
   | 0 => 0
   | S m => if is_i (f m) then S (count_paulis m f) else count_paulis m f
  end.


Fixpoint long_z' (n:nat) (f: nat -> paulimat) (j:nat) :=
  match n with
   | 0 => (fun (_:R) => I 1)
   | S m => if is_i (f m) || (j =? 0)
            then (fun (t:R) => (long_z' m f j t) ⊗ (I 2))
            else if j =? 1
                 then fun (t:R) => long_z' m f 0 t ⊗ (phase_shift t)
                 else fun (t:R) => (long_z' m f (j-1) t ⊗ ∣0⟩⟨0∣) .+ (long_z' m f (j-1) (Ropp t) ⊗ ∣1⟩⟨1∣)
  end.

Fixpoint add_front (n:nat) (f: nat -> paulimat) :=
  match n with
   | 0 => I 1
   | S m => match (f m) with
              | paulix => add_front m f ⊗ hadamard
              | pauliy => add_front m f ⊗ ((phase_shift (PI / (IZR 2))) × hadamard)
              | _ => I 2
            end
  end.

Fixpoint add_end (n:nat) (f:nat -> paulimat) :=
  match n with
   | 0 => I 1
   | S m => match (f m) with
              | paulix => add_end m f ⊗ hadamard
              | pauliy => add_end m f ⊗ (hadamard × (phase_shift (- (PI / (IZR 2)))))
              | _ => I 2
            end
  end.


Definition exp_paulis (n:nat) (t:R) (f: nat -> paulimat) :=
  (add_front n f) × (long_z' n f (count_paulis n f) t) × (add_end n f).



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

Fixpoint mid_paulis_aux (n:nat) (amp:R) f v j :=
  match n with
   | 0 => EG.SKIP
   | S m => if is_i (f m) || (j =? 0)
            then mid_paulis_aux m amp f v j
            else if j =? 1
                 then EG.useq ((EG.CX v m)) (EG.useq (EG.U1 ((IZR 2) * amp) m) ((EG.CX v m)))
                 else EG.useq ((EG.CX v m)) (EG.useq (mid_paulis_aux m amp f m (Nat.sub j 1)) (EG.CX v m))
  end.

Fixpoint mid_paulis (n:nat) (amp:R) f j :=
  match n with
   | 0 => EG.SKIP
   | S m => if is_i (f m)
            then mid_paulis m amp f j
            else if j =? 0 then EG.SKIP
            else if j =? 1 then EG.U1 ((IZR 2) * amp) m
            else (mid_paulis_aux m amp f m (Nat.sub j 1))
  end.

Definition synth_digital_ibm_apauli (n:nat) (t:R) (f: nat -> paulimat) :=
 EG.useq (front_half n f) (EG.useq (mid_paulis n t f (count_paulis n f)) (EG.invert (front_half n f))).

Open Scope nat_scope.

Theorem synth_digital_ibm_pauli_correctness: forall (n : nat) (t : R) (f : nat->paulimat), 0 < n ->
  exp_paulis n t f = EG.uc_eval n (synth_digital_ibm_apauli n t f).
Proof.
  intros.
  unfold exp_paulis,synth_digital_ibm_apauli,EG.uc_eval.
  induction n; simpl in *. inv H.
  destruct n; simpl in *.
  destruct (f 0); simpl in *; unfold pad_u,pad.
  bdestruct (0 + 1 <=? 1); try lia.
  rewrite eval_H.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  rewrite I_rotation.
  rewrite phase_shift_rotation.
  rewrite <- phase_adjoint.
  rewrite <- phase_shift_rotation.
  rewrite I_rotation.
  simpl in *.
  gridify.
  bdestruct (0 + 1 <=? 1); try lia.
  rewrite eval_H.
  replace R0 with (IZR Z0); try (easy; simpl in *).
  repeat rewrite phase_shift_rotation.
  repeat rewrite <- phase_adjoint.
  repeat rewrite <- phase_shift_rotation.
  rewrite I_rotation. simpl in *.
  repeat rewrite kron_1_r.
  repeat rewrite kron_1_l; try auto_wf.
  rewrite id_adjoint_eq.
  rewrite Mmult_1_l; try auto_wf.
  repeat rewrite Mmult_1_r; try auto_wf.
  rewrite phase_shift_rotation.
  rewrite phase_adjoint.
  rewrite Mmult_assoc.
  rewrite Mmult_assoc.
  replace ((hadamard × (hadamard × phase_shift (- (PI / 2)))))
          with (((hadamard × hadamard) × phase_shift (- (PI / 2)))); try (rewrite Mmult_assoc; easy).
  replace ((hadamard × (hadamard × phase_shift ((PI / 2))))) 
          with (((hadamard × hadamard) × phase_shift ((PI / 2)))); try (rewrite Mmult_assoc; easy).
  replace (hadamard × hadamard) with (I 2) by (rewrite MmultHH; easy).
  gridify.
  repeat rewrite phase_mul.
  R_field_simplify.
  replace (Rplus (PI / IZR 2) (- (PI / IZR 2))) with (IZR 0) by lra.
  replace (Rplus (- (PI / IZR 2)) (PI / IZR 2)) with (IZR 0) by lra.
  easy.
Admitted.




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

