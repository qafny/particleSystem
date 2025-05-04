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
Definition stype := nat.

Inductive H : Type :=
  | HAnni: stype -> H
  | HCreator: stype -> H.
  
(* Pauli string *)
Inductive paulimat: Type :=
| paulix             (* X = [[0;1]; [1;0] ] *)
| pauliy             (* Y = [[0;-i]; [i;0]] *)
| pauliz             (* Z = [[1;0]; [0;-1]] *)
| paulii.

Definition lowprog_app := list paulimat.
(* lowprog_ten: (amplitude, length, f: index -> element *)
Definition lowprog_ten := (C * nat * (nat -> lowprog_app)) %type.
Definition lowprog := list lowprog_ten.

(* (a x b) x (c x d), all items are tensor *)
Definition ten_ten_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  let '((z1, m), f) := p1 in
  let '((z2, n), g) := p2 in   
  (Cmult z1 z2, m+n, fun x => if x <? m then f x else g (x-m)). 

(* (a + b) x (c + d) *)
Fixpoint plus_ten_plus (p1: lowprog) (p2: lowprog) : lowprog := 
  match p1 with [] => p2
  | x::ax => let fix helper (t: lowprog_ten) (tl: lowprog) : lowprog:=
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
      | (z1, 0, g) => (z1, 0, g)
      | (z1, n, g) => (z1, n, fun x => a ++ (g x))
      end) in  
      ten_ten_ten (ten_app_ten_helper m' f p2) (helper1 (f m') p2)
    end.


Definition ten_app_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  match p1 with
  | (z, m, f) => ten_app_ten_helper m f p2
  end.
        
Fixpoint plus_app_plus (p1 p2: lowprog) : lowprog :=
  match p1 with [] => p2
  | x::ax => let fix helper (a : lowprog_ten) (l : lowprog) : lowprog :=  
    (match l with [] => []
    | b :: bx => (ten_app_ten a b) :: (helper a bx)
    end) in
  (helper x p2) ++ (plus_app_plus ax p2)
  end.

Definition plus_plus_plus (p1 p2: lowprog) : lowprog := p1 ++ p2.


(* transformation for boson qubit mapping *)
(* ladder operator *)
Definition ladder_anni : lowprog :=
  let x := fun x => [paulix] in
  let y := fun x => [pauliy] in
[(RtoC (1/2), 1, x); (Cmult Ci (RtoC (1/2)), 1, y)].

Definition ladder_creator : lowprog :=
  let x := fun x => [paulix] in
  let y := fun x => [pauliy] in
[(RtoC (1/2), 1, x); (Cmult (-Ci) (RtoC (1/2)), 1, y)].

(* ∣1⟩⟨1∣= 1/2(I−Z) *)
Definition projector : lowprog :=
  let x := fun x => [paulii] in
  let y := fun x => [pauliz] in
[(RtoC (1/2), 1, x); (Cmult (-C1) (RtoC (1/2)), 1, y)]. 


(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb 
loop pos from (0,0) to (Nb-1, Nb) when in application
*)

Fixpoint mult_ampli_hplus (z : C) (p : lowprog) : lowprog :=
  let helper (t : lowprog_ten) : lowprog_ten := 
    match t with (z1, m, f) => (Cmult z z1, m, f) end in
  match p with [] => []
  | x :: ax => (helper x) :: (mult_ampli_hplus z ax)
  end.

(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Definition boson_creator (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (sqrt (INR (n + 1))) in
    let left : lowprog := [(C1, n, fun x => [paulii])] in
    let right : lowprog := [(C1, Nb-n-1, fun x => [paulii])] in 
    let mid : lowprog := (plus_ten_plus ladder_anni ladder_creator) in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_plus_plus (plus_plus_plus left mid1) right 
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => term 0
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb =? 0 then [] else helper (Nb - 1).

(* b_i = SUM_{1 to Nb} sqrt(n) I_0 x ... x (-)_(n-1) x (+)_(n) ... x I_Nb *)
Definition boson_annihilator (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (sqrt (INR n)) in
    let left : lowprog := [(C1, n - 1, fun _ => [paulii])] in
    let right : lowprog := [(C1, Nb - n, fun _ => [paulii])] in
    let mid : lowprog := plus_ten_plus ladder_creator ladder_anni in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_ten_plus (plus_ten_plus left mid1) right
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => []
    | 1 => term 1
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb <? 1 then [] else helper Nb.
  
(* n_i = SUM_{0 to Nb} n_i I_0 x ... |1><1|_ni ... x I_Nb *)
Definition boson_numerator (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (INR n) in
    let left : lowprog := [(C1, n, fun _ => [paulii])] in
    let right : lowprog := [(C1, Nb - n, fun _ => [paulii])] in
    let mid : lowprog := mult_ampli_hplus amp projector in
    plus_ten_plus (plus_ten_plus left mid) right
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => term 0
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb <? 0 then [] else helper Nb.


(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n *)
Definition fermion_creator (id n : nat) : lowprog :=
  let left : lowprog := [(C1, n-1, fun _ => [pauliz])] in
  plus_ten_plus left ladder_creator.

Definition fermion_anni (id n : nat) : lowprog :=
  let left : lowprog := [(C1, n-1, fun _ => [pauliz])] in
  plus_ten_plus left ladder_anni.
  