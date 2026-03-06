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

Definition psi := list (C * basisKet).

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.

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



(* Particle Type Flag *)
Inductive particle : Set := 
  | Fem (* fermion t(2) *) 
  | Bos (x:nat). (* boson t(m) *) 


Definition iota : Set := (list particle). 
(*
Definition stype := nat.
*)

Inductive typeflag : Set := PLAIN | U | HER. 

Definition tauType : Set := typeflag * iota.

Inductive blueExp := 
        | HId 
        | HAnni
        | HDag (x:blueExp)
        | HPlus (x:blueExp) (y:blueExp)
        | HApp (x:blueExp) (y:blueExp)
        | HTensor (x:blueExp) (y:blueExp).



(* highprog MUST be in canonical form *)
Inductive hsnd : Type :=
  | anni: particle -> hsnd
  | creator: particle -> hsnd
  | hunit: particle -> hsnd.
   
(* highprog_ten: (amplitude, length, f: index -> (site_id, hsnd) *)
Definition highprog_ten := (C * nat * (nat -> list hsnd)) %type.

(* (# of qubits of each site) * (e1 x e2 ..) *)
(* require for each term to have the same length of qubits: [a+ 3; a 2; I 10], then 
all the other terms should also be 15. *)
Definition highprog := list highprog_ten.

(* Pauli string *)
Inductive paulimat: Type :=
| paulix             (* X = [[0;1]; [1;0] ] *)
| pauliy             (* Y = [[0;-i]; [i;0]] *)
| pauliz             (* Z = [[1;0]; [0;-1]] *)
| paulii.

(* lowprog_ten: (amplitude, length, f: index -> element *)
Definition lowprog_ten := (C * (nat -> paulimat)) %type.
Definition lowprog := list lowprog_ten.

Definition norm_ten := (R * (nat -> paulimat)) %type.
Definition norm_prog := list norm_ten.

(* unitary gate exp(-i r ZZZ) *)
Definition ugate := (R * (nat -> paulimat)) %type.


(* syntax lib functions. *)
Definition is_i (s:paulimat) :=
   match s with paulii => true | _ => false end.
