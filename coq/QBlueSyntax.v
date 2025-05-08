Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
(* Local Open Scope nat_scope. 

Coercion INR : nat >-> R. *)

(* This document contains the syntax of QBlue, which is an extension of Lambda/mu calculus 
   with second quantization.
   The inductive relation equiv defines the expression equivalence relations.
 *)

(* Define m, n, j, k as natural numbers; z as complex numbers *)

(* single particle basis vector with at most m states, eta = |k> *)

(* Particle Type Flag *)
Inductive particle : Set := 
  | fermi (* fermion *)
  | bos. (* boson *)

Definition stype := (particle * nat) %type.

Inductive hsnd : Type :=
  | anni: stype -> hsnd
  | creator: stype -> hsnd.
  
(* highprog_ten: (amplitude, length, f: index -> (site_id, hsnd) *)
Definition highprog_ten := (C * nat * (nat -> list (nat * hsnd))) %type.

(* (# of qubits of each site) * (e1 x e2 ..) *)
Definition highprog := ((list nat) * (list highprog_ten)) %type.
