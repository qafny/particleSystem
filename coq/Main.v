Require Import List.
Import ListNotations.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueCompile.


Definition exp1 := HPlus HId HAnni.
Definition it1 := Fem :: nil.

Definition exp2 := HTensor HAnni HId.
Definition it2 := Fem :: (Bos 4%nat) :: nil.

Definition err : R := R1.
Definition t : R := R1.

Definition lowp := translate_highp2circ err t exp2 it2 (length it2).



