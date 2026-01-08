Require Import Reals.
Require Import QuantumLib.Matrix.


Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynth.



(*
Theorem synth_analog_digital_correctness: forall (t : R) (lp : lowprog_ten),
  lp', ulist = Cal t n lp
  Matrix(exp_ugate t lp) = synth_digital lp' ulist.
Proof.
    
Qed. *)



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

