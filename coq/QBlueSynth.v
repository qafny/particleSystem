(* Do synthesization upon different hardware *)

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.


(* This is the input for sythesization *)
Parameter exp_ugate : R -> lowprog_ten -> ugate. (* exp(-i r H) *)


(* 2. to gates of IBM analog, X, Z, ZZ gates *)
(* fill_pl 3 2 X => I tensor I tensor X *)
Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if eqb x a then true else inb eqb a xs
  end.

Definition fill_pl (reg : list nat) (p : paulimat) : lowprog_ten :=
  let f := (fun id => if (inb Nat.eqb id reg) then p else paulii) in (C1, f).


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

(* Find the nonI in pauli_str. qid starts from the length of pauli_str. *)
Fixpoint find_nonI (qid : nat) (pauli_str : nat -> paulimat) : list nat :=
  match qid with 
  | 0 %nat => []
  | S n => let aux := find_nonI n pauli_str in
    (if (paulimat_eqb (pauli_str n) paulii) then aux else n :: aux)
  end.  

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

Definition synth_analog_ibm (t : R) (nbit : nat) (pauli_str : nat -> paulimat) 
  : list ugate :=
  let ml := find_nonI nbit pauli_str in 
  if Nat.leb (length ml) 2 then
    let mid := exp_ugate t (fill_pl ml pauliz) in
    let (left, right) := synth_analog_ibm_helper ml nbit pauli_str in
    left ++ [mid] ++ right
  else [].


(* 3. Input is any-local, to gates of Indiana analog, Convert to Z, X...X basis *)
Fixpoint synth_analog_indiana_helper (ml : list nat) (nbit : nat) (pauli_str : nat -> paulimat) : 
  (list ugate) * (list ugate) :=
  match ml with 
  | [] => ([], [])
  | m :: ax => let (left, right) := synth_analog_indiana_helper ax nbit pauli_str in
    let hu := H_u m in
    let su := S_u m in 
    let sdagu := SDag_u m in
    let (app1, app2) := 
      match (pauli_str m) with 
      | pauliy => (su, sdagu)
      | pauliz => (hu, hu)
      | _ => ([], []) 
      end in
    (left ++ app1, app2 ++ right) end.

Definition synth_analog_indiana (t : R) (nbit : nat) (pauli_str : nat -> paulimat) 
  : list ugate :=
  let ml := find_nonI nbit pauli_str in 
  let mid := exp_ugate t (fill_pl ml paulix) in
  let (left, right) := synth_analog_indiana_helper ml nbit pauli_str in
  left ++ [mid] ++ right.



