(* This document contains the semantics of QBlue *) 

Require Import Reals.
Require Import Coq.Strings.String.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueCompiler.
(* Local Open Scope nat_scope. 

Coercion INR : nat >-> R. *)

(* Single ket semantics, apply a or a+ to a single eta state: a^[+] |k> 
return single-element list: [(z, signle-element nat list)] *)
Definition single_sem (flag : bool) (z:C) (k m : nat) : phi :=
  if flag then
    (if k =? m then [(z, [])] else [(Cmult z (RtoC (sqrt (INR (k + 1)))), [Nat.add k 1])])
  else
    (if k =? 0 then [(z, [])] else [(Cmult z (RtoC (sqrt (INR k))), [Nat.sub k 1])]).
  
(* helper function to combine two quantum states *)
(* if two lists are equal *)
Fixpoint eq_list (x y : list nat) : bool :=
  match x, y with
  | [], [] => true
  | a :: xx, b :: yy => if true then eq_list xx yy else false
  | _, _ => false
  end.

Fixpoint subcombine (a : ket) (qs : phi) : phi :=
  match qs with 
  | [] => [a]
  | (x,y)::xs => 
    if (eq_list (snd a) y) then (Cplus (fst a)  x, y)::(subcombine a xs) else (x,y)::xs
  end.

Fixpoint combine (phi1 phi2: phi) : phi:=
  match phi1 with 
    | [] => phi2
    | x::xs => subcombine x (combine xs (phi2))
  end.

(* helper func for S-TEN *)
Definition appendList (a b : phi) : phi :=
  match a, b with 
  (* for tensor operation, the two inputs must be kets with the same amplitudes *)
  | [(z1, al)], [(z2, bl)] => [(Cmult z1 z2, al ++ bl)]
  | _, _ => []
  end.

(* semanics for creator / annihilator. *)  
Inductive sem_highprog_snd : hsnd -> phi -> phi -> Prop :=
  | s_anni: forall m ptc z j, sem_highprog_snd (anni ptc m) ([(z,[j])]) (single_sem false z j m)
  | s_crea: forall z ptc m j, sem_highprog_snd (creator ptc m) ([(z,[j])]) (single_sem true z j m)
  | s_unit: forall m s, sem_highprog_snd (hunit m) s s.

(* semanics for e1 o e2 o ... en, the first nat is site id in the corresponding state phi*)  
Inductive sem_highprog_app : nat -> list hsnd -> phi -> phi -> Prop :=
  | s_app_empty: forall sid s, sem_highprog_app sid [] s s
  | s_app_next: forall sid opfst oplist sini s1 s2, sem_highprog_app sid oplist sini s1 ->
    sem_highprog_snd opfst s1 s2 ->
    sem_highprog_app sid (opfst :: oplist) sini s2.

(* semanics for e1 x e2 x ... en. *)  
Inductive sem_highprog_tensor : highprog_ten -> phi -> phi -> Prop :=
  | s_ten_empty: forall z f s, sem_highprog_tensor (z, 0%nat, f) s s
  | s_ten_next: forall z f n sini smid sfinal,
    sem_highprog_app (S n) (f (S n)) sini smid ->
    sem_highprog_tensor (z, n, f) smid sfinal ->
    sem_highprog_tensor (z, S n, f) sini sfinal.

(* semanics for e1 + e2 + ... en. *) 
Inductive sem_highprog_plus : highprog -> phi -> phi -> Prop :=
  | s_plus_empty: forall s, sem_highprog_plus [] s s
  | s_plus_next: forall sini opten oplist s1 s2,
    sem_highprog_tensor opten sini s1 -> 
    sem_highprog_plus oplist sini s2 ->
    sem_highprog_plus (opten :: oplist) sini (combine s1 s2).

(* Q1. apply e2... en first, then e1
Q2. let snd just apply to the first of the state
Q3. paulix, y, how to write? We have canceled out the list
*)
    (*
Inductive sem_lowp : lowprog -> phi -> phi -> Prop :=
  | sem_plus_empty: forall st, sem_lowp [] st st
  | sem_plus_next: forall st1 st2 eten eplus, sem_lowp 


Inductive sem : hsnd -> phi -> phi -> Prop :=
  (* s_move *)
  | s_move_anni: forall m z j, sem (anni (_, m)) ([(z,[j])]) (single_sem false z j m)
  | s_move_crea: forall z m j, sem (creator (_, m)) ([(z,[j])]) (single_sem true z j m)
  (* s_sum *)
  | s_sum: forall e1 e2 phi phi1 phi2, sem e1 phi phi1 -> sem e2 phi phi2 -> 
            sem (HPlus e1 e2) phi (combine phi1 phi2)
  (* s_par *)
  | s_par: forall e phi1 phi1' phi2 phi2', sem e phi1 phi1' -> sem e phi2 phi2' ->
            sem e (phi1 ++ phi2) (combine phi1' phi2')
  (* s_app *)
  | s_app: forall e1 e2 phi phi' phi'', sem e2 phi phi' -> sem e1 phi' phi'' ->
            sem (HApp e1 e2) phi phi''
  (* s_tensor *)
  | s_tensor: forall e1 e2 w w' phi phi', sem e1 w phi -> sem e2 w' phi' ->
            sem (HTensor e1 e2) (w ++ w') (appendList phi phi').

Inductive sem_lowp_snd : hsnd -> phi -> phi -> Prop :=

*)
