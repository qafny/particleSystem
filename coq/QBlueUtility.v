(* Define the unitilies, including numbers etc *)
Require Import Reals.
Require Export QuantumLib.Complex.

Definition myC1 := RtoC (R1).
Definition R2 : R := R1 + R1.
Definition R4 : R := R1 + R1 + R1 + R1.
Definition R7 : R := R1 + R2 + R4.

Parameter Rceil_Z : R -> Z.

Definition Rceil_nat (x : R) : nat :=
  Z.to_nat (Rceil_Z x).

