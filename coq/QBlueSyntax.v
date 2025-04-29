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

(* Hamiltonion expression *)
Inductive H : Type :=
  | HAnni 
  | HCreator.
  
(* Pauli string *)
Inductive paulimat: Type :=
| paulix             (* X = [[0;1]; [1;0] ] *)
| pauliy             (* Y = [[0;-i]; [i;0]] *)
| pauliz             (* Z = [[1;0]; [0;-1]] *)
| paulii.

Definition lowprog_app := list paulimat.
Definition lowprog_ten := (nat * (nat -> lowprog_app)) %type.
Definition lowprog := (C * (list lowprog_ten)) %type.

(* (a x b) x (c x d), all items are tensor *)
Definition ten_ten_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  let (m, f) := p1 in
  let (n, g) := p2 in   
  (m+n, fun x => if x <? m then f x else g (x-m)). 

(* (a + b) x (c + d) *)
Fixpoint plus_ten_plus (p1: list lowprog_ten) (p2: list lowprog_ten) : list lowprog_ten := 
  match p1 with [] => p2
  | x::ax => let fix helper (t: lowprog_ten) (tl: list lowprog_ten) : list lowprog_ten:=
    (match tl with [] => []
    | y::ay => (ten_ten_ten t y) :: (helper t ay) 
    end) in
  (helper x p2) ++ (plus_ten_plus ax p2)
  end.

(* (a x b) o (c x d) *)
Fixpoint ten_app_ten_helper (m: nat) (f: nat -> lowprog_app) (p2: lowprog_ten) : lowprog_ten :=
  match m with
  | 0 => p2
  | S m' =>
    let fix helper1 (a: lowprog_app) (b: lowprog_ten) : lowprog_ten :=  
      (match b with
      | (0, g) => (0, g)
      | (n, g) => (n, fun x => a ++ (g x))
      end) in  
      ten_ten_ten (ten_app_ten_helper m' f p2) (helper1 (f m') p2)
    end.

Definition ten_app_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  match p1 with
  | (m, f) => ten_app_ten_helper m f p2
  end.
        


(* transformation for boson qubit mapping 
Definition boson_mapping (hexp : list (nat -> list H)) : list (nat -> list paulimat) :=
*)
