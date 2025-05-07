Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
(* Local Open Scope nat_scope. *)

Coercion INR : nat >-> R.

(* This document contains the syntax of QBlue, which is an extension of Lambda/mu calculus 
   with second quantization.
   The inductive relation equiv defines the expression equivalence relations.
 *)

(* Define m, n, j, k as natural numbers; z as complex numbers *)

(* single particle basis vector with at most m states, eta = |k> *)

(* Hamiltonion expression *)
Definition stype := nat.

(* Particle Type Flag *)
Inductive xi := 
  | f (* fermion *)
  | b. (* boson *)

Inductive hsnd : Type :=
  | anni: stype -> xi -> hsnd
  | creator: stype -> xi -> hsnd.
  
(* highprog_ten: (amplitude, length, f: index -> (site_id, hsnd) *)
Definition highprog_ten := (C * nat * (nat -> list (nat * hsnd))) %type.
Definition highprog := list highprog_ten.
