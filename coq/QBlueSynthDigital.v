(* Do synthesization upon digital hardware using SQIR IR
https://github.com/inQWIRE/SQIR/tree/main/SQIR *)
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.
From VOQC Require Import FullGateSet.
From VOQC Require Import Main.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.

Module EG := ExtractionGateSet.
Module FG := FullGateSet.


(* convert X and Y to Z base *)
Definition cvt2base (curbit: nat) (s : paulimat) : 
  EG.ucom EG.U :=
  match s with 
  | paulix => EG.H curbit
  | pauliy => EG.useq (EG.U1 (PI / R2) curbit) (EG.H curbit) 
  | _ => EG.SKIP
  end.

Fixpoint cvt_all (nbit:nat) (pauli_str : nat -> paulimat) : EG.ucom EG.U :=
  match nbit with 
   | 0 => EG.SKIP
   | S m => EG.useq (cvt2base m (pauli_str m)) (cvt_all m  pauli_str)
  end. 

(* generate gate for each paulimat: Z => CNOT I CNOT *)
(* useq a b means in the matrix of applying a first and then b, like b . a*)
Definition abit_cx (curbit tarbit : nat) (s : paulimat) : 
  EG.ucom EG.U :=
  match s with 
  | paulii => EG.SKIP
  | _ => EG.CX curbit tarbit 
  end.

Fixpoint abit_cx_all (curbit tarbit:nat) (f : nat -> paulimat) :=
  match curbit with
   | 0 => EG.SKIP
   | S m => if is_i (f m) then abit_cx_all m tarbit f else EG.useq (abit_cx_all m curbit f) (EG.CX curbit tarbit)
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
     None => EG.SKIP
   | Some m => 
     let mid := EG.U1 (R2 * amp) m in
     let half := EG.useq (cvt_all m f) (abit_cx_all m m f) in
     EG.useq (EG.useq half mid) (EG.invert half)
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
Definition synth_digital_ibm_single (t : R) (nbit : nat) (amp:C) f := 
  (synth_digital_ibm_apauli (t * (fst amp)) nbit f).
   

Fixpoint synth_digital_ibm_raw (t : R) (nbit : nat) (input : lowprog) (acc: EG.ucom EG.U)
  : EG.ucom EG.U :=
  match input with
  | [] => acc
  | (amp, f) :: app => 
  synth_digital_ibm_raw t nbit app (EG.useq acc (synth_digital_ibm_apauli (t * (fst amp)) nbit f))
  end.


Definition is_SKIP (c : EG.ucom EG.U) : bool :=
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
Fixpoint prune_SKIP (c : EG.ucom EG.U) : EG.ucom EG.U :=
  match c with
  | EG.useq c1 c2 =>
      let c1' := prune_SKIP c1 in
      let c2' := prune_SKIP c2 in
      if is_SKIP c1' then c2'
      else if is_SKIP c2' then c1'
      else EG.useq c1' c2'
  | _ => c
  end.

Definition synth_digital_ibm t nbit input := prune_SKIP (synth_digital_ibm_raw t nbit input EG.SKIP).

Fixpoint ucom_gate_count (circ : EG.ucom EG.U) : nat :=
  match circ with
  | EG.useq c1 c2 => ucom_gate_count c1 + ucom_gate_count c2
  | EG.uapp _ _ => 1%nat
  end.


(* Convert from ExtractionGateSet to FullGateSet so can use optimization in VOQC *)
Fixpoint cvt_egate_fullgate (dim : nat) (u : EG.ucom EG.U) : full_ucom_l dim :=
  match u with
  | EG.useq u1 u2 =>
      match (cvt_egate_fullgate dim u1), (cvt_egate_fullgate dim u2) with
      | l1, l2 => l1 ++ l2
      end

  | EG.uapp g qs =>
      match g, qs with
      | EG.U_X, q :: nil => [App1 FG.U_X q]
      | EG.U_H, q :: nil => [App1 FG.U_H q]
      | EG.U_U1 r, q :: nil => [App1 (FG.U_U1 r) q]
      | EG.U_U2 r1 r2, q :: nil => [App1 (FG.U_U2 r1 r2) q]
      | EG.U_U3 r1 r2 r3, q :: nil => [App1 (FG.U_U3 r1 r2 r3) q]

      | EG.U_CX, q1 :: q2 :: nil => [App2 FG.U_CX q1 q2]
      | EG.U_SWAP, q1 :: q2 :: nil => [App2 FG.U_SWAP q1 q2]

      | EG.U_CCX, q1 :: q2 :: q3 :: nil => [App3 FG.U_CCX q1 q2 q3]

      (* unreachable if you decompose first *)
      | _, _ => nil
      (* | EG.U_CU1 _, _
      | EG.U_CH, _
      | EG.U_CCU1 _, _
      | EG.U_CSWAP, _
      | EG.U_C3X, _
      | EG.U_C4X, _ => [] *)
      end 
  end.


Definition voqc_count_total (dim : nat) (l : VOQC.Main.circ dim) := count_total l.
Definition voqc_count_H (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_H l.
Definition voqc_count_X (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_X l.
Definition voqc_count_CX (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_CX l.
Definition voqc_count_Rzq (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_Rzq l.
Definition voqc_count_U1 (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_U1 l.
Definition voqc_count_U2 (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_U2 l.
Definition voqc_count_U3 (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.count_U3 l.
Definition voqc_convert_to_rzq (dim : nat) (l : VOQC.Main.circ dim) := VOQC.Main.convert_to_rzq l.
Definition voqc_swap_route (dim : nat) (l : VOQC.Main.circ dim) := VOQC.Main.swap_route l.
Definition voqc_decompose_swaps (dim : nat)  (l : VOQC.Main.circ dim) := VOQC.Main.decompose_swaps l.
Definition voqc_optimize (dim : nat) (l : VOQC.Main.circ dim) := VOQC.Main.optimize l.
Definition voqc_make_lnn_ring := VOQC.Main.make_lnn_ring.
Definition voqc_trivial_layout := VOQC.Main.trivial_layout.
Definition voqc_lnn_ring_path_finding_fun := VOQC.Main.lnn_ring_path_finding_fun.


Definition ibmdigi_to_rzq (nbit : nat) (circ : EG.ucom EG.U) : VOQC.Main.circ nbit := 
  let c0 := decompose_to_voqc_gates circ in
  let c1 := cvt_egate_fullgate nbit c0 in
  voqc_convert_to_rzq nbit c1.

Definition ibmdigi_voqc_optimize (nbit : nat) (circ : EG.ucom EG.U) : VOQC.Main.circ nbit :=
  let c2 := ibmdigi_to_rzq nbit circ in
  let cg := voqc_make_lnn_ring nbit in
  let la := voqc_trivial_layout nbit in
  let c3 := voqc_decompose_swaps nbit (voqc_swap_route nbit c2 la cg (voqc_lnn_ring_path_finding_fun nbit)) cg in
  voqc_optimize nbit c3.
