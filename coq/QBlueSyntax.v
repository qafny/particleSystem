Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Local Open Scope nat_scope.

Coercion INR : nat >-> R.

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
  | HPlus : H -> H -> H                        (* e + e *)
  | HApp : H -> H -> H.                       (* e e *)

(* To make sure all programs are in canonical forms
e.g., only the followings are allowed:
a, a+, (any e1) + (any e2),
(e1 e2)⊗e3, e1(e2⊗e3) *)
Inductive canonicalCheck : bool -> H -> Prop := 
  | canonicalCheckAnni: forall c s m f, canonicalCheck f (HAnni c s m)
  | canonicalCheckHDag: forall c s m f, canonicalCheck f (HDag (HAnni c s m)) 
  (* within dagger only HAnni is allowed. *)
  | canonicalCheckHTensor: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HTensor e1 e2)
  | canonicalCheckHPlus: forall e1 e2 f, canonicalCheck f e1 -> canonicalCheck f e2
    -> canonicalCheck false (HPlus e1 e2)
  | canonicalCheckHApp: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HApp e1 e2).

(* Pauli string *)
Inductive paulimat: Type :=
| paulix : C -> paulimat            (* X = c*[[0;1]; [1;0] ] *)
| pauliy : C -> paulimat            (* Y = c*[[0;-i]; [i;0]] *)
| pauliz : C -> paulimat           (* Z = c*[[1;0]; [0;-1]] *)
| paulii : C -> paulimat.


(* Hamiltonian type after transformation.
Nested structure: (plus (tensor (app )))) *)
Definition lowprog := list (list (list paulimat)).

(* ladder operator *)
Definition ladder_anni (coef : R) : lowprog :=
[[[paulix (Cmult C1 (RtoC ((1/2) * coef)))]]; [[pauliy ((Cmult (-Ci) (RtoC ((1/2) * coef))))%C]]].  

Definition ladder_creator (coef : R) : lowprog :=
[[[paulix (Cmult C1 (RtoC ((1/2) * coef)))]]; [[pauliy ((Cmult Ci (RtoC ((1/2) * coef))))%C]]].  

(* projection operator |1><1| *)
Definition projection_op (coef : R): lowprog :=
[[[paulii (Cmult C1 (RtoC ((1/2) * coef)))]]; [pauliz (Cmult (-C1) (RtoC ((1/2) * coef)))]].

(* Boson-qubit mapping *)
(* 1st, id for sum; 2nd id for tensor *)
Definition posi := nat * nat. 

(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Definition boson_creator (pos : posi) : lowprog :=
  let (p1, p2) = pos in (* p1 is the id of the term in sum, p2 the one in tensor *)
  if p1 =? p2 then ladder_anni (1)
  else if p1 + 1 =? p2 then ladder_creator (sqrt (p2))
  else [[[paulii]]]

(* b_i = SUM_{1 to Nb} sqrt(n) I_0 x ... x (-)_(n-1) x (+)_(n) ... x I_Nb *)
Definition boson_anni (pos : posi) : lowprog :=
  let (p1, p2) = pos in (* p1 is the id of the term in sum, p2 the one in tensor *)
  if p1 =? p2 then ladder_creator (1)
  else if p1 + 1 =? p2 then ladder_anni (sqrt (p2))
  else [[[paulii]]]

(* n_i = SUM_{0 to Nb} n_i I_0 x ... |1><1|_ni ... x I_Nb *)
Definition boson_n (pos : posi) : lowprog := 
  let (p1, p2) = pos in (* p1 is the id of the term in sum, p2 the one in tensor *)
  if p1 =? p2 then projection_op (p2)
  else [[[paulii]]]

(* I_i = I_0 x I_1 ... x I_Nb *)
(*
Fixpoint I (Nb: nat): lowprog :=
  match Nb with 
  | 0 => [[[[paulii]]]]
  | S n => [[[paulii]]]] :: (I n)
  end.

(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Fixpoint boson_anni (Nb : nat) : lowprog:= 
  let qbit (idx : nat) := 
    let pre := if idx =? 0 then [] else I (idx-1) in
    let post := if idx =? (Nb-1) then [] else I (Nb-idx-2) in
    pre ++ (ladder_anni 1) ++ (ladder_creator (sqrt (idx+1))) ++ post
  in 
  match Nb with 
  | 0 => []
  | S n => (boson_anni n) ++ (qbit n)
  end.

(* b_i = SUM_{1 to Nb} sqrt(n) I_0 x ... x (-)_(n-1) x (+)_(n) ... x I_Nb *)
Fixpoint boson_creator (Nb : nat) : lowprog :=
  let qbit (idx : nat) :=
    if idx =? 0 then [] else (* start from n=1 *)
    let pre := if idx <? 2 then [] else I (idx - 2) in
    let post := if idx =? Nb then [] else I (Nb - idx - 1) in
    pre ++ (ladder_creator 1) ++ (ladder_anni (sqrt (idx))) ++ post
  in
  match Nb with
  | 0 => []
  | S n => (boson_creator n) ++ (qbit n)
  end.

Definition op_mult (a b : lowprog) : lowprog :=
  flat_map (fun x =>
    map (fun y => x ++ y) b
  ) a.

(* number operator: ni = b_i^+ b_i *)
Definition boson_n (Nb : nat) : lowprog :=
  op_mult (boson_anni Nb) (boson_creator Nb).
*)

(* Jordan-Wigner transformation for fermions *)

