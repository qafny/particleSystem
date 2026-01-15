(* Do synthesization upon digital hardware using SQIR IR
https://github.com/inQWIRE/SQIR/tree/main/SQIR *)
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* convert X and Y to Z base *)
Definition cvt2base (nbit curbit tarbit : nat) (s : paulimat) : 
  ucom ExtractionGateSet.U :=
  match s with 
  | paulix => H curbit
  | pauliy => useq (U1 (PI / R2) curbit) (H curbit) 
  | _ => SKIP
  end.

(* generate gate for each paulimat: Z => CNOT I CNOT *)
Definition ucom_abit (nbit curbit tarbit : nat) (s : paulimat) : 
  ucom ExtractionGateSet.U :=
  match s with 
  | paulii => SKIP
  | _ => if curbit =? tarbit 
    then 
      cvt2base nbit curbit tarbit s
    else
      useq (CX curbit tarbit) (cvt2base nbit curbit tarbit s) 
  end.


(* generate the seq of gates for one pauli string *)
(* nbit: # of bits in circuit; curbit: current bit; pauli_str: pauli string
NOTE: CNOT gates have the bit 0 as target *)
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


(* Synthesization of IBM digital
return: sequence of unitary gate of the converted circuit *)
Fixpoint synth_digital_ibm (t : R) (nbit : nat) (input : lowprog) 
  : ucom ExtractionGateSet.U :=
  match input with
  | [] => SKIP
  | (amp, _, f) :: app => useq (synth_digital_ibm_apauli (t * (fst amp)) nbit f) 
  (synth_digital_ibm t nbit app)
  end.
