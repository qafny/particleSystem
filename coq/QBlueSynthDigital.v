(* Do synthesization upon digital hardware using SQIR IR
https://github.com/inQWIRE/SQIR/tree/main/SQIR *)
Require Import QuantumLib.Matrix.
From SQIR Require Import SQIR.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


Definition dag_base_Unitary {k} (u : base_Unitary k) : base_Unitary k :=
  match u with
  | U_R a b c => U_R (-a) (-c) (-b) 
  | U_CNOT    => U_CNOT
  end.

Fixpoint dag_ucom {dim} (g : base_ucom dim) : base_ucom dim :=
  match g with
  | useq g1 g2      => useq (dag_ucom g2) (dag_ucom g1)
  | uapp1 u n       => uapp1 (dag_base_Unitary u) n
  | uapp2 u m n     => uapp2 (dag_base_Unitary u) m n
  | uapp3 u a b c   => uapp3 (dag_base_Unitary u) a b c
  end.


(* To basic gates of CNOT, H, Rz, Collect parity on the first qubit *)
(* Map X and Y to Z, X = HZH, Y = Rz(pi/2) HZH Rz(-pi/2) *)
(* nbit: # of bits in circuit; curbit: id of the pauli in the string; s: the current pauli to convert 
return: the converting matrix: for Y, return Rz; H and H; Rz) *)

(* convert X and Y to Z base *)
Definition cvt2base (nbit curbit tarbit : nat) (s : paulimat) : base_ucom nbit :=
  match s with 
  | paulix => H curbit
  | pauliy => useq (H curbit) (P curbit)
  | _ => SKIP
  end.

(* generate gate for each paulimat: Z => CNOT I CNOT *)
Definition ucom_abit (nbit curbit tarbit : nat) (s : paulimat) : base_ucom nbit :=
  match s with 
  | paulii => SKIP
  | _ => if curbit =? tarbit 
    then 
      cvt2base nbit curbit tarbit s
    else
      useq (cvt2base nbit curbit tarbit s) (CNOT curbit tarbit)
  end.


(* generate the seq of gates for one pauli string *)
(* nbit: # of bits in circuit; curbit: current bit; pauli_str: pauli string
NOTE: CNOT gates have the bit 0 as target *)
Fixpoint helper_digital_ibm_ulist (nbit curbit : nat) (pauli_str : nat -> paulimat)
  : base_ucom nbit := 
  let tarbit := 0%nat in
  let aux := ucom_abit nbit curbit tarbit (pauli_str curbit) in
  match curbit with
  | 0 => aux
  | S cur' => useq aux (helper_digital_ibm_ulist nbit cur' pauli_str)
  end.


Definition synth_digital_ibm_apauli (amp : C) (nbit : nat) (pauli_str : nat -> paulimat)
  : base_ucom nbit := 
  (* Rz(2r) = exp(-irZ), NOTE: should have prove amp is real in trotter *)
  let mid := Rz (R2 * (fst amp)) nbit in
  let ulist := helper_digital_ibm_ulist nbit 0%nat pauli_str in
  useq (dag_ucom ulist) (useq mid ulist).


(* Synthesization of IBM digital
return: sequence of unitary gate of the converted circuit *)
Fixpoint synth_digital_ibm (t : R) (nbit : nat) (input : lowprog) : base_ucom nbit :=
  match input with
  | [] => SKIP
  | (amp, _, f) :: app => useq (synth_digital_ibm_apauli (t * amp) nbit f) (synth_digital_ibm t nbit app)
  end.


