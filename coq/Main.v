Require Import List.
Import ListNotations.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueCompile.


Definition exp1 := HPlus HId HAnni.
Definition it1 := Fem :: nil.

Definition exp2 := HTensor HAnni HId.
Definition it2 := Fem :: (Bos 4%nat) :: nil.

Definition c1 := myC1.
Definition m1 : nat := ceilR_N R4.


Definition err : R := R1.
Definition t : R := R1.

Definition lowp := translate1 err t exp2 it2 (length it2).



