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
Definition eta (m : nat) := { k : nat | k < m }.

(* n particle ket state: w ::= z · TENSOR η_k *)
Definition ket (m n : nat) := list (eta m). 
Definition ket_state (m n : nat) := (C * ket m n)%type.

(* Quantum state phi ::= SUM w_j | O *)
Inductive qstate (m n : nat) : Set :=
  | QSuperpos : list (ket_state m n) -> qstate m n
  | QZero : qstate m n.

(* Quantum State type l ::= t(m) | l TENSOR l *)

Definition stype := nat.

Inductive iota : Set :=
  | QtBase : stype -> iota        (* t(m): a single-particle state *)
  | QtTensor : iota -> iota -> iota.  (* l TENSOR l *)

(* Data Type Flag *)
Inductive zeta := 
  | p (* Ordinary matrix *)
  | h. (* Hermitian matrix *)

(* Quantum Operation Type *)
Inductive tau : Type := F: zeta -> iota -> tau.

(* Hamiltonion expression *)
Inductive H : Type :=
  | HAnni : C -> zeta -> stype -> H             (* z · F^f(t(m)) *)
  | HDag : H -> H                             (* e+ *)
  | HTensor : H -> H -> H                     (* e T e *)
  | HAdd : H -> H -> H                        (* e + e *)
  | HApp : H -> H -> H.                       (* e e *)
