(* This document contains the semantics of QBlue *) 

Require Import Reals.
Require Import Coq.Strings.String.
Require Import Psatz.
Require Import QBlue.QBlueSyntax.
Require Import QuantumLib.Complex.
Local Open Scope nat_scope.


Coercion INR : nat >-> R.

(* Single ket semantics, apply a or a+ to a single eta state: a^[+] |k> 
return single-element list: [(z, signle-element nat list)] *)
Definition single_sem (flag : bool) (z:C) (k m : nat) : phi :=
  if flag then
    (if k =? m then [(z, [])] else [(Cmult z (RtoC (sqrt ( k + 1 ))), [k + 1])])
  else
    (if k =? 0 then [(z, [])] else [(Cmult z (RtoC (sqrt k)), [k - 1])]).
  
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
  | [(z1, al)], [(z2, bl)] => [(z1, al ++ bl)]
  | _, _ => []
  end.


Inductive sem : H -> phi -> phi -> Prop :=
  (* s_move *)
  | s_move_anni: forall z zeta m j, sem (HAnni z zeta m) ([(z,[j])]) (single_sem false z j m)
  | s_move_crea: forall z zeta m j, sem (HDag (HAnni z zeta m)) ([(z,[j])]) (single_sem true z j m)
  (* s_sum *)
  | s_sum: forall e1 e2 phi phi1 phi2, sem e1 phi phi1 -> sem e2 phi phi2 -> 
            sem (HAdd e1 e2) phi (combine phi1 phi2)
  (* s_par *)
  | s_par: forall e phi1 phi1' phi2 phi2', sem e phi1 phi1' -> sem e phi2 phi2' ->
            sem e (combine phi1 phi2) (combine phi1' phi2')
  (* s_app *)
  | s_app: forall e1 e2 phi phi' phi'', sem e2 phi phi' -> sem e1 phi' phi'' ->
            sem (HApp e1 e2) phi phi''
  (* s_tensor *)
  | s_tensor: forall e1 e2 w w' phi phi', sem e1 w phi -> sem e2 w' phi' ->
            sem (HTensor e1 e2) (appendList w w') (appendList phi phi').


