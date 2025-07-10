(* This document contains the semantics of QBlue *) 

Require Import Reals.
Require Import Coq.Strings.String.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.VectorStates.
Require Import QBlue.QBlueSyntax.
Require Import QBlueType.
(* Local Open Scope nat_scope. 

Coercion INR : nat >-> R. *)
Definition create_sem (m:nat) (b:nat) : option (C * nat) :=
  if b <? m then Some (RtoC (sqrt (INR (b+1))), Nat.add b 1) else None.


Definition anni_sem (m:nat) (b:nat) : option (C * nat) :=
  if b =? 0 then None else Some (RtoC (sqrt (INR b)), Nat.sub b 1).

Local Open Scope nat_scope.

Inductive forall_map (P:psi -> psi -> Prop) : psi -> psi -> Prop :=
    forall_map_empty : forall_map P nil nil
  | forall_map_many: forall x y s1 s2, P ([x]) y -> forall_map P s1 s2 -> forall_map P (x::s1) (y++s2).

Definition nleft (f:nat -> nat) (n:nat) := fun i => f (i + n).

Fixpoint allFem (t:iota) (f:nat -> nat) :=
  match t with [] => 0
             | Fem::xl => f 0 + allFem xl (nleft f 1)
             | (Bos a)::xl => allFem xl (nleft f 1)
  end.

Definition ketCombine (n:nat) (f1 f2:nat -> nat) :=
  fun i => if i <? n then f1 i else f2 (i-n).

Fixpoint subcombine (n:nat) (a : (C * basisKet)) (qs : psi) : psi :=
  match qs with 
  | [] => []
  | (x,y)::xs => (Cmult (fst a) x, ketCombine n (snd a) y)::subcombine n a xs
  end.

Fixpoint combine (n:nat) (phi1 phi2: psi) : psi:=
  match phi1 with 
    | [] => []
    | x::xs => subcombine n x (combine n xs (phi2))
  end.

Inductive blue_sem : nat -> iota -> blueExp -> psi -> psi -> Prop := 
   s_id : forall n t s, blue_sem n t HId s s
 | f_anni_1: forall n s, anni_sem 2 (snd s 0) = None -> blue_sem n ([Fem]) HAnni ([s]) (nil)
 | f_anni_2: forall n s c m, anni_sem 2 (snd s 0) = Some (c,m)
               -> blue_sem n ([Fem]) HAnni ([s]) ([(fst s, (update (snd s) 0 m))])
 | f_crea_1: forall n s, create_sem 2 (snd s 0) = None -> blue_sem n ([Fem]) (HDag HAnni) ([s]) (nil)
 | f_crea_2: forall n s c m, create_sem 2 (snd s 0) = Some (c,m)
               -> blue_sem n ([Fem]) (HDag HAnni) ([s]) ([(fst s, (update (snd s) 0 m))])
 | b_anni_1: forall n j s, anni_sem j (snd s 0) = None -> blue_sem n ([Bos j]) HAnni ([s]) (nil)
 | b_anni_2: forall n j s c m, anni_sem j (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) HAnni ([s]) ([(fst s, (update (snd s) 0 m))])
 | b_crea_1: forall n j s, create_sem j (snd s 0) = None -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) (nil)
 | b_crea_2: forall n j s c m, create_sem j (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) ([(fst s, (update (snd s) 0 m))])
 | s_top: forall n t e s s1, forall_map (blue_sem n t e) s s1 -> blue_sem n t e s s1
 | s_ten: forall n t1 t2 e1 e2 w s1 s2, blue_sem n t1 e1 ([w]) s1 
                 -> blue_sem (n+allFem t1 (snd w)) t2 e2 ([(C1, nleft (snd w) (length t1))]) s2
                 -> blue_sem n (t1++t2) (HTensor e1 e2) ([w]) (combine (length t1) s1 s2)
 | s_app: forall n t e1 e2 s s1 s2, blue_sem n t e2 s s1 
                 -> blue_sem n t e1 s1 s2
                 -> blue_sem n t (HApp e1 e2) s s2
 | s_plus: forall n t e1 e2 s s1 s2, blue_sem n t e1 s s1 
                 -> blue_sem n t e2 s s2
                 -> blue_sem n t (HPlus e1 e2) s (s1++s2).

Inductive WFKet : iota -> basisKet -> Prop := 
  WFEmpty : forall s, WFKet nil s
 | WFManyF : forall xl s, s 0 < 2 -> WFKet xl (nleft s 1) -> WFKet (Fem::xl) s
 | WFManyB : forall m xl s, s 0 < m -> WFKet xl (nleft s 1) -> WFKet (Bos m::xl) s.

Definition WFState (t:iota) (s:psi) := forall e, In e s -> WFKet t (snd e).


(* Theorem: type soundness *)
Theorem type_right_matrix: forall ia e, typing ia e (H, ia) ->  rewrites_recur ia (HDag e) e.
Proof.
  intros. induction H; try easy.
Admitted.  

Theorem type_soundness: forall ia e t n s, typing ia e t -> WFState ia s -> exists s', blue_sem n ia e s s' /\ WFState ia s'.
Proof.
  intros. induction H; try easy.
Admitted.
