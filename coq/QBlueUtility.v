(* Define the unitilies, including numbers etc *)
Require Import Reals.
Require Export QuantumLib.Complex.

Definition myC1 := RtoC (R1).
Definition R2 : R := R1 + R1.
Definition R4 : R := R1 + R1 + R1 + R1.
Definition R7 : R := R1 + R2 + R4.

Parameter ceilR_N: R -> nat. 
Parameter ceilR_Z: R -> Z. 
