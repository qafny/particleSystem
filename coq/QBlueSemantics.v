(* This document contains the semantics of QBlue *) 

Require Import Reals.
Require Import Coq.Strings.String.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueCompiler.
(* Local Open Scope nat_scope. 

Coercion INR : nat >-> R. *)

(* Single ket semantics, apply a (false) or a+ to a single eta state: a^[+] |k> 
k: current state; m: boundary; return (C, nat) *)
Definition op_asite (flag : bool) (k m : nat) : option (R * nat) :=
  if flag then
    (if k =? m then None else Some (sqrt (INR (k + 1)), Nat.add k 1))
  else
    (if k =? 0 then None else Some (sqrt (INR k), Nat.sub k 1)).
 
(* replace the pos_th element in ll with newv *)
Fixpoint replace_nth {A : Type} (pos : nat) (newv : A) (ll : list A) : list A :=
  match pos, ll with
  | 0, _ :: xs => newv :: xs                     
  | S n, x :: xs => x :: replace_nth n newv xs   
  | _, [] => []                                  
  end.

(* creator operates on a tensor term.
flag: creator/anni; sid: site id; m: boundary of this operator; input: a term of tensor *)
Definition op_aterm (flag : bool) (sid m : nat) (input : ket) : ket :=
  let (amp, nlist) := input in
  match nth_error nlist sid with 
  | None => (amp, [])
  | Some k => match (op_asite flag k m) with
    | None => (amp, [])
    | Some (factor, newv) => 
    let newl := replace_nth sid newv nlist in (Cmult amp factor, newl)
    end
  end.
  
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
    if (eq_list (snd a) y) then (Cplus (fst a) x, y)::(subcombine a xs) else (x,y)::xs
  end.

Fixpoint combine (phi1 phi2: phi) : phi:=
  match phi1 with 
    | [] => phi2
    | x::xs => subcombine x (combine xs (phi2))
  end.

Fixpoint sem_hsnd (flag : bool) (sid m : nat) (input : phi) : phi :=
  match input with 
  | [] => []
  | k :: kl => subcombine (op_aterm flag sid m k) (sem_hsnd flag sid m kl)
  end.

(*
(* helper func for S-TEN *)
Definition appendList (a b : phi) : phi :=
  match a, b with 
  (* for tensor operation, the two inputs must be kets with the same amplitudes *)
  | [(z1, al)], [(z2, bl)] => [(Cmult z1 z2, al ++ bl)]
  | _, _ => []
  end.
*)

(* semanics for creator / annihilator. *)  
Inductive sem_highprog_snd : nat -> hsnd -> phi -> phi -> Prop :=
  | s_anni: forall sid m ptc s, sem_highprog_snd sid (anni ptc m) s (sem_hsnd false sid m s)
  | s_crea: forall sid m ptc s, sem_highprog_snd sid (creator ptc m) s (sem_hsnd true sid m s)
  | s_unit: forall sid m s, sem_highprog_snd sid (hunit m) s s.

(* semanics for e1 o e2 o ... en, the first nat is site id in the corresponding state phi*)  
Inductive sem_highprog_app : nat -> list hsnd -> phi -> phi -> Prop :=
  | s_app_empty: forall sid s, sem_highprog_app sid [] s s
  | s_app_next: forall sid opfst oplist sini s1 s2, sem_highprog_app sid oplist sini s1 ->
    sem_highprog_snd sid opfst s1 s2 ->
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


(* The following translate the state into qubit-based 
and define the semantics for low-level program *)
Fixpoint genl_helper (v len : nat) : list nat :=
  match len with 0 => []
  | S n => v :: (genl_helper v n)
  end.

(* Ex: |3> (m=5) ==> |0 0 0 1 0 0> *)
Definition translate_to_bistate_siteh (k m : nat) : list nat :=
  let left : list nat := genl_helper 0%nat k in
  let right : list nat := genl_helper 0%nat (Nat.sub m k) in
  left ++ (1%nat :: right).

(* input: a m-based ket; boundary: m for each site *)
Fixpoint translate_to_bistate_keth (input : list nat) (boundary : list nat) : list nat :=
  match input, boundary with 
  | [], _ => []
  | k :: kl, m :: ml => 
    let cur : list nat := translate_to_bistate_siteh k m in
    let rem : list nat := translate_to_bistate_keth kl ml in
    cur ++ rem
  | _, [] => []
  end.

(* translate state from natural-number-based to qubit-based *)
Definition translate_to_bistate (input : ket) (boundary : list nat) : ket :=
  let (amp, klist) := input in (amp, translate_to_bistate_keth klist boundary).

(* semanics for pauli strings. *)
Definition op_pauli (op : paulimat) (k : nat) : (C * nat) :=
  match op with 
  | paulii => (C1, k)
  | paulix => (C1, Nat.sub 1 k)
  | pauliy => if k =? 0 then (Ci, 1%nat) else (-Ci, 0%nat)
  | pauliz => if k =? 0 then (C1, 0%nat) else (-C1, 1%nat)
  end.

(* creator operates on a tensor term in binary.
op: paulimat; sid: site id; input: a term of tensor *)
Definition op_pauli_aterm (op : paulimat) (sid : nat) (input : ket) : ket :=
  let (amp, nlist) := input in
  match nth_error nlist sid with 
  | None => (amp, [])
  | Some k => let (factor, newv) := op_pauli op k in 
    let newl := replace_nth sid newv nlist in (Cmult amp factor, newl)
  end.

Fixpoint sem_pauli (op : paulimat) (sid : nat) (input : phi) : phi :=
  match input with 
  | [] => []
  | k :: kl => subcombine (op_pauli_aterm op sid k) (sem_pauli op sid kl)
  end.

(* site id; pauli operator; input state; output state *)
Inductive sem_lowprog_snd : nat -> paulimat -> phi -> phi -> Prop :=
  | s_move_pauli: forall op sid s, sem_lowprog_snd sid op s (sem_pauli op sid s).

(* semanics for e1 x e2 x ... en. *)  
Inductive sem_lowprog_tensor : lowprog_ten -> phi -> phi -> Prop :=
  | s_tenl_empty: forall z f s, sem_lowprog_tensor (z, 0%nat, f) s s
  | s_tenl_next: forall z f n sini smid sfinal,
    sem_lowprog_snd (S n) (f (S n)) sini smid ->
    sem_lowprog_tensor (z, n, f) smid sfinal ->
    sem_lowprog_tensor (z, S n, f) sini sfinal.

(* semanics for e1 + e2 + ... en. *) 
Inductive sem_lowprog_plus : lowprog -> phi -> phi -> Prop :=
  | s_plusl_empty: forall s, sem_lowprog_plus [] s s
  | s_plusl_next: forall sini opten oplist s1 s2,
    sem_lowprog_tensor opten sini s1 -> 
    sem_lowprog_plus oplist sini s2 ->
    sem_lowprog_plus (opten :: oplist) sini (combine s1 s2).

(*
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
*)
