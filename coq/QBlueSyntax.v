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

(* n particle ket state: w ::= z · TENSOR eta_k, each element is a site *)
Definition ket := (C * list nat) %type.

(* Quantum state phi ::= SUM w_j | O *)
Definition phi := list ket. 


(* Particle Type Flag *)
Inductive particle : Set := 
  | electron (* electron *) 
  | proton 
  | neutron 
  | nue (* nu_e *)
  | numu 
  | bos. (* boson *)

Definition stype := nat.

Inductive hsnd : Type :=
  | anni: particle -> stype -> hsnd
  | creator: particle -> stype -> hsnd
  | hunit: stype -> hsnd.
   
(* highprog_ten: (amplitude, length, f: index -> (site_id, hsnd) *)
Definition highprog_ten := (C * nat * (nat -> list hsnd)) %type.

(* (# of qubits of each site) * (e1 x e2 ..) *)
(* require for each term to have the same length of qubits: [a+ 3; a 2; I 10], then 
all the other terms should also be 15. *)
Definition highprog := list highprog_ten.
