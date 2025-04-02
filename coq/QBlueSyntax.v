Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Local Open Scope nat_scope.


(* This document contains the syntax of QBlue, which is an extension of Lambda/mu calculus 
   with second quantization.
   The inductive relation equiv defines the expression equivalence relations.
 *)

(* Define m, n, j, k as natural numbers; z as complex numbers *)

(* single particle basis vector with at most m states, eta = |k> *)
Definition eta := nat.

(* n particle ket state: w ::= z · TENSOR eta_k *)
Definition ket := (C * list eta) %type.

(* Quantum state phi ::= SUM w_j | O *)
Definition phi := list ket. 
(* OK to neglect O? *)

(* Quantum State type l ::= t(m) | l TENSOR l *)
Definition stype := nat.
(* t(m) is a list with single element *)
Definition iota : Set := list stype.

(* Data Type Flag *)
Inductive xi := 
  | p (* Ordinary matrix *)
  | h. (* Hermitian matrix *)

(* Quantum Operation Type *)
Definition tau : Type := xi * iota.

(* Hamiltonion expression *)
Inductive H : Type :=
  | HAnni : C -> xi -> stype -> H             (* z · F^f(t(m)) *)
  | HDag : H -> H                             (* e+ *)
  | HTensor : H -> H -> H                     (* e T e *)
  | HAdd : H -> H -> H                        (* e + e *)
  | HApp : H -> H -> H.                       (* e e *)

