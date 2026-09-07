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


(* exp(-i r H) *)
Definition exp_ugate (t : R) (lp_ten : nat -> paulimat) : ugate :=
  (t, lp_ten).


(* 2. to gates of IBM analog, X, Z, ZZ gates *)
(* fill_pl 3 2 X => I tensor I tensor X *)
Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if eqb x a then true else inb eqb a xs
  end.

Definition fill_pl (reg : list nat) (p : paulimat) : (nat -> paulimat) :=
  let f := (fun id => if (inb Nat.eqb id reg) then p else paulii) in f.


(* H = exp(-i pi/4 X) exp(-i pi/4 Z) exp(-i pi/4 X). For IBM *)
(* H unitary gate on X and Z basis.
   nbit: # of bits in circuit; qid: id of the current bit *)
Definition H_u (qid : nat) : list ugate := 
  let xu := exp_ugate (PI/R4) (fill_pl [qid] paulix) in
  let zu := exp_ugate (PI/R4) (fill_pl [qid] pauliz) in
  xu :: zu :: xu :: nil. 

(* S = exp(-i pi/4 Z) *)
Definition S_u (qid : nat) : list ugate := 
  let zu := exp_ugate (PI/R4) (fill_pl [qid] pauliz) in zu :: nil.

(* S^+ = exp(-i 7 pi/4 Z) *)
Definition SDag_u (qid : nat) : list ugate := 
  let zu := exp_ugate (R7 * PI/R4) (fill_pl [qid] pauliz) in zu :: nil. 

(* Scan for non-I entries, but stop immediately once there are more than 2. *)
Fixpoint find_nonI_bounded_aux (qid remaining : nat) (pauli_str : nat -> paulimat)
  (acc : list nat) : option (list nat) :=
  match qid with
  | 0 %nat => Some (rev acc)
  | S n =>
    if paulimat_eqb (pauli_str n) paulii then
      find_nonI_bounded_aux n remaining pauli_str acc
    else
      match remaining with
      | 0 %nat => None
      | S remaining' => find_nonI_bounded_aux n remaining' pauli_str (n :: acc)
      end
  end.

Definition find_nonI (qid : nat) (pauli_str : nat -> paulimat) : option (list nat) :=
  find_nonI_bounded_aux qid 2 pauli_str [].

(* Input is 2-local. Convert to X, Z, ZZ basis *)
Fixpoint synth_analog_ibm_helper (ml : list nat) (nbit : nat) (pauli_str : nat -> paulimat) : 
  (list ugate) * (list ugate) :=
  match ml with 
  | [] => ([], [])
  | m :: ax => let (left, right) := synth_analog_ibm_helper ax nbit pauli_str in
    let hu := H_u m in
    let su := S_u m in 
    let sdagu := SDag_u m in
    let (app1, app2) := 
      match (pauli_str m) with 
      | paulix => (hu, hu)
      | pauliy => (su ++ hu, hu ++ sdagu)
      | _ => ([], []) 
      end in
    (left ++ app1, app2 ++ right) end.

Definition synth_analog_ibm_single (r : R) (nbit : nat) (pauli_str : nat -> paulimat) 
  : list ugate :=
  match find_nonI nbit pauli_str with
  | Some ml =>
    let mid := exp_ugate r (fill_pl ml pauliz) in
    let (left, right) := synth_analog_ibm_helper ml nbit pauli_str in
    left ++ [mid] ++ right
  | None => []
  end.

Definition synth_analog_ibm (t : R) (nbit : nat) (input : lowprog) : list ugate :=
  rev (fold_left (fun acc b =>
    rev_append (synth_analog_ibm_single (Rmult t (fst (fst b))) nbit (snd b)) acc) input []).

Fixpoint check_2local (nbit : nat) (lp : lowprog) : bool :=
  match lp with
  | [] => true
  | (_, f) :: ax =>
    match find_nonI nbit f with
    | None => false
    | Some _ => check_2local nbit ax
    end
  end.


(* Translate to Indiana Analog hardware *)
Fixpoint syn_analog_indiana_x' (nbit:nat) (f : nat -> paulimat) : nat -> paulimat :=
  match nbit with
    0 => fun _ => paulii
  | S m => if is_i (f m) 
           then syn_analog_indiana_x' m f 
           else fun i => if i =? m then paulix else syn_analog_indiana_x' m f i
  end.
Definition syn_analog_indiana_x (t:R) (nbit:nat) (f : nat -> paulimat) : ugate :=
    (t, syn_analog_indiana_x' nbit f).


(* Helper: builds result without repeated ++ on growing acc *)
Fixpoint syn_analog_indiana_a_dl (nbit:nat) (f : nat -> paulimat)
  (accf : list ugate -> list ugate) : (list ugate -> list ugate) :=
  match nbit with
  | 0 => accf
  | S m =>
    match f m with
    | pauliy =>
      let left := (Rdiv PI R4, (fun i => if i =? m then pauliz else paulii)) in
      let right := (Rdiv (Rmult R7 PI) R4, (fun i => if i =? m then pauliz else paulii)) in
      syn_analog_indiana_a_dl m f (fun tl => left :: (accf (right :: tl)))
    | pauliz =>
      let v1 := (Rdiv PI R4, (fun i => if i =? m then paulix else paulii)) in
      let v2 := (Rdiv PI R4, (fun i => if i =? m then pauliz else paulii)) in
      syn_analog_indiana_a_dl m f
        (fun tl => v1 :: v2 :: v1 :: (accf (v1 :: v2 :: v1 :: tl)))
    | _ => syn_analog_indiana_a_dl m f accf
    end
  end.

Definition syn_analog_indiana_a (nbit:nat) (f : nat -> paulimat) (acc: list ugate) : list ugate :=
  syn_analog_indiana_a_dl nbit f (fun tl => rev_append (rev acc) tl) [].

Definition synth_analog_indiana_single (r : R) (nbit : nat) (f : nat -> paulimat) : list ugate :=
  syn_analog_indiana_a nbit f [syn_analog_indiana_x r nbit f].

Definition synth_analog_indiana (t:R) (nbit:nat) (input : lowprog) : list ugate :=
  rev (fold_left (fun acc b =>
    rev_append (synth_analog_indiana_single (Rmult t (fst (fst b))) nbit (snd b)) acc) input []).

(*
Fixpoint syn_analog_indiana_a (nbit:nat) (f : nat -> paulimat) (acc: list ugate) : list ugate :=
  match nbit with 
    0 => acc
  | S m => 
     match f m with 
       pauliy => 
          syn_analog_indiana_a m f 
            ((Rdiv PI R4, (fun i => if i =? m then pauliz else paulii))
                ::acc++[((Rdiv (Rmult R7 PI) R4), (fun i => if i =? m then pauliz else paulii))])
       | pauliz => 
          let v := (Rdiv PI R4, fun i => if i =? m then paulix else paulii)
                      ::(Rdiv PI R4, fun i => if i =? m then pauliz else paulii)
                      ::(Rdiv PI R4, fun i => if i =? m then paulix else paulii)::[] in
          syn_analog_indiana_a m f (v++acc++v)
       | _ => syn_analog_indiana_a m f acc
      end
   end.


Definition synth_analog_indiana (t:R) (nbit:nat) (input : lowprog) : list ugate :=
  fold_left (fun a b => synth_analog_indiana_single (Rmult t (fst (fst b))) nbit (snd b)::a) input [].
*)
