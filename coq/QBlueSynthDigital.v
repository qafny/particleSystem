(* Do synthesization upon digital hardware using SQIR IR
https://github.com/inQWIRE/SQIR/tree/main/SQIR *)
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* convert X and Y to Z base *)
Definition cvt2base (curbit: nat) (s : paulimat) : 
  ucom ExtractionGateSet.U :=
  match s with 
  | paulix => H curbit
  | pauliy => useq (U1 (PI / R2) curbit) (H curbit) 
  | _ => SKIP
  end.

Fixpoint cvt_all (nbit:nat) (pauli_str : nat -> paulimat) :=
  match nbit with 
   | 0 => SKIP
   | S m => useq (cvt2base m (pauli_str m)) (cvt_all m  pauli_str)
  end. 

(* generate gate for each paulimat: Z => CNOT I CNOT *)
(* useq a b means in the matrix of applying a first and then b, like b . a*)
Definition abit_cx (curbit tarbit : nat) (s : paulimat) : 
  ucom ExtractionGateSet.U :=
  match s with 
  | paulii => SKIP
  | _ => (CX curbit tarbit) 
  end.

Fixpoint abit_cx_all (curbit tarbit:nat) (f : nat -> paulimat) :=
  match curbit with
   | 0 => SKIP
   | S m => if is_i (f m) then abit_cx_all m tarbit f else useq (abit_cx_all m curbit f) (CX curbit tarbit)
  end.

Fixpoint find_last_abit (n : nat) (f : nat -> paulimat) :=
   match n with
    | 0 => None
    | S m => if is_i (f m) then find_last_abit m f else Some m
   end.

(* generate the seq of gates for one pauli string *)
(* nbit: # of bits in circuit; curbit: current bit; pauli_str: pauli string
NOTE: CNOT gates have the bit 0 as target *)

Definition synth_digital_ibm_apauli (amp : R) (n : nat) (f: nat -> paulimat) :=
  match find_last_abit n f with
     None => SKIP
   | Some m => 
     let mid := U1 (R2 * amp) m in
     let half := useq (cvt_all m f) (abit_cx_all m m f) in
     useq (useq half mid) (invert half)
  end.

(*
Fixpoint helper_digital_ibm_ulist (nbit curbit tarbit: nat) (pauli_str : nat -> paulimat)
  : ucom ExtractionGateSet.U := 
  let aux := if Nat.ltb curbit nbit then 
    ucom_abit nbit curbit tarbit (pauli_str curbit) 
    else SKIP
  in
  match curbit with
  | 0 => aux
  | S cur' => useq aux (helper_digital_ibm_ulist nbit cur' tarbit pauli_str)
  end.


Definition synth_digital_ibm_apauli (amp : R) (nbit : nat) (pauli_str : nat -> paulimat)
  : ucom ExtractionGateSet.U := 
  match nbit with
  | 0 => SKIP
  | S n =>
    let tarbit := 0%nat in
    (* Rz(2r) = exp(-irZ), NOTE: should have prove amp is real in trotter *)
    let mid := U1 (R2 * amp) nbit in
    let ulist := helper_digital_ibm_ulist nbit n tarbit pauli_str in
    useq (useq ulist mid) (invert ulist)
  end.
*)

(* Synthesization of IBM digital
return: sequence of unitary gate of the converted circuit *)
Fixpoint synth_digital_ibm_raw (t : R) (nbit : nat) (input : lowprog) (acc: ucom ExtractionGateSet.U)
  : ucom ExtractionGateSet.U :=
  match input with
  | [] => acc
  | (amp, f) :: app => synth_digital_ibm_raw t nbit app (useq acc (synth_digital_ibm_apauli (t * (fst amp)) nbit f))
  end.


Definition is_SKIP (c : ucom ExtractionGateSet.U) : bool :=
  match c with
  | uapp g qs =>
      match g, qs with
      | ExtractionGateSet.U_U1 r, q :: nil =>
          if Reqb r R0 then Nat.eqb q 0 else false
      | _, _ => false
      end
  | _ => false
  end.


(* Filter out the SKIP gates, avoid too big qasm files *)
Fixpoint prune_SKIP (c : ucom ExtractionGateSet.U) : ucom ExtractionGateSet.U :=
  match c with
  | useq c1 c2 =>
      let c1' := prune_SKIP c1 in
      let c2' := prune_SKIP c2 in
      if is_SKIP c1' then c2'
      else if is_SKIP c2' then c1'
      else useq c1' c2'
  | _ => c
  end.

Definition synth_digital_ibm t nbit input := prune_SKIP (synth_digital_ibm_raw t nbit input SKIP).

