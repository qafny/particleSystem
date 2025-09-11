Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueCompiler.
Local Open Scope R_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

From SQIR Require Import SQIR. 


Definition exp1 := HPlus HId HAnni.
Definition it1 := Fem :: nil.

Definition exp2 := HTensor HAnni HId.
Definition it2 := Fem :: (Bos 4) :: nil.



Definition run_test (exp : blueExp) (it : iota) : list ugate := 
  let lowp := bexp_to_lowprog exp2 it2 in
  let fix helper (pro : lowprog) :=  
    match pro with
    | (C, n, pau) :: ax => (synth_analog_ibm 1 n pau) ++ (helper ax)
    | _ => []
    end in
  helper lowp.

Compute run_test exp2 it2.
Compute run_test exp1 it1.
