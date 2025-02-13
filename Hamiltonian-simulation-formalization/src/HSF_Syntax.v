(* -- HSF_Syntax.v -- *)
(**
 * Here we define the abstract syntax of a Hamiltonian evolution program.
 *
 * We added the HSF prefix because there is already a module named "Syntax" in the standard library.
 * HSF stands for "Hamiltonian simulation formalization".
 *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Reals.
Require Import PauliRotations.
Require Export QWIRE.Matrix.

(* Our representation of a real number expression *)
Inductive HScalar :=
    | HScAdd (s1 s2 : HScalar)
    | HScMult (s1 s2 : HScalar)
    | HScSub (s1 s2 : HScalar)
    | HScDiv (s1 s2 : HScalar)
    | HScExp (s : HScalar)
    | HScCos (s : HScalar)
    | HScSin (s : HScalar)
    | HScReal (r : R) (literal : string)
        (* Recording the string for trotterization *).

(* A Pauli operator, applied to a named qubit *)
Inductive HPauli := HIdOp (loc : string) (p : Pauli).

(* A multiplicative product of the two types defined above *)
Record TIH_Term := makeTIH_Term
{
    hScale : HScalar;
    hPaulis : list HPauli;
}.

(**
 * This models an "instruction" of a Hamiltonian program,
 * which consists of a Hamiltonian operator together with a duration to apply it.
 *
 * A Hamiltonian operator is a sum of TIH_Terms.
 *
 * The TermId field is unused. It is carried over from Yu-Xiang's syntax.
 *)
Record HSF_Term := makeHSF_Term
{
    TermId : string;
    Duration : HScalar;
    Hamiltonian : list TIH_Term;
}.

(**
 * A Hamiltonian evolution program has two sections.
 * The user first declare a set of named qubits.
 * Next, the user specifies a list of instructions to apply onto those qubits.
 *)
Record H_Program := makeHProg
{
    Decls : list string;
    Terms : list HSF_Term;
}.

(* Planck's constant, found in Schrodinger's equation. *)
(* I have a feeling that this doesn't belong here. *)
Definition h_bar : R := (6.62607015 / (10 ^ 34)) / (2 * PI).
Definition one_over_h_bar : R := 1 / h_bar.
