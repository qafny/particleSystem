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

(* factorial *)
Fixpoint factor (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * factor k
  end.

Fixpoint Cpow (c : C) (n : nat) : C :=
  match n with
  | O   => C1
  | S k => c * Cpow c k
  end.

