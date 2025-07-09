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

(* quantum state syntax. *)
Definition vector := nat.

Definition basisKet := nat -> nat.

Definition psi := list basisKet.

(*
Definition parstate : Type := (C * spinbase).

Definition sigma : Set := nat.

Definition partype :Set := nat * nat.

Definition qtype : Set := list partype.

Inductive typeflag : Set := P | U | H. 

Inductive ttype : Set := TType (q:qtype) | IType (q:qtype) | FType (tv:typeflag) (q:qtype).

Coercion TType : qtype >-> ttype.

Inductive type : Set := CT | QTy (t:ttype) | FTy (t1:type) (t2:type).

Coercion QTy : ttype >-> type.
*)


(* n particle ket state: w ::= z · TENSOR eta_k, each element is a site 

Definition ket := (C * list nat) %type.
*)


(* Quantum state phi ::= SUM w_j | O *)
Definition iota : Set := nat * (nat -> nat). 


(* Particle Type Flag *)
Inductive particle : Set := 
  | electron (* electron *) 
  | proton 
  | neutron 
  | nue (* nu_e *)
  | numu 
  | bos. (* boson *)

Definition stype := nat.

Definition tauType :Set := particle * iota.

Inductive blueExp := 
        | HApp (x:blueExp) (y:blueExp)
        | HPlus (x:blueExp) (y:blueExp)
        | HTensor (x:blueExp) (y:blueExp)
        | HDag (x:blueExp)
        | Anni (x:particle) (n:stype)
        | HId (x:particle) (n:stype).




(* Canaoncal form *)

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
