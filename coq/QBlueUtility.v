(* Define the unitilies, including numbers etc *)
Require Import Reals.
Require Export QuantumLib.Complex.

Definition R2 : R := R1 + R1.
Definition R4 : R := R1 + R1 + R1 + R1.
Definition R7 : R := R1 + R2 + R4.

Parameter ceilR_N: R -> nat. 

(* get the smaller Real value *)
Parameter Rltb : R -> R -> bool.

(* Random generator, given a max bound r, return uniformly from [0, r)*)
Parameter random_float : R -> R.
