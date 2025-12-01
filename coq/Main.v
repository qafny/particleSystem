Require Import List.
Import ListNotations.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueCompile.


Definition exp1 := HPlus HId HAnni.
Definition it1 := Fem :: nil.

Definition exp2 := HTensor HAnni HId.
Definition it2 := Fem :: (Bos 4) :: nil.

Definition c1 := myC1.
Definition err : R := 0.1.
Definition t : R := 0.1.
Definition lowp := translate err t exp2 it2. 


(* entry for running compiler 
 
Definition run_test (exp : blueExp) (it : iota) : list ugate := 
  let lowp := bexp_to_lowprog exp it in
  let fix helper (pro : lowprog) :=  
    match pro with
    | (C, n, pau) :: ax => (synth_analog_ibm 1 n pau) ++ (helper ax)
    | _ => []
    end in
  helper lowp.

Compute run_test exp2 it2.
Compute run_test exp1 it1. *)


