Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.

Local Open Scope nat_scope.

(* This document contains the syntax of MuQ, which is an extension of Lambda/mu calculus with second quantization.
   The inductive relation equiv defines the expression equivalence relations.
 *)

Definition var := nat.

Definition spinbase : Type := (nat -> nat).

Definition allzero := fun (_:nat) => 0.

Definition zerostate := fun (_:nat) => (C0, allzero).

Definition parstate : Type := (C * spinbase).

Definition sigma : Set := nat.

Definition partype :Set := nat * nat.

Definition qtype : Set := list partype.

Inductive typeflag : Set := P | U | H. 

Inductive ttype : Set := TType (q:qtype) | IType (q:qtype) | FType (tv:typeflag) (q:qtype).

Coercion TType : qtype >-> ttype.

Inductive type : Set := CT | QTy (t:ttype) | FTy (t1:type) (t2:type).

Coercion QTy : ttype >-> type.

Inductive exp := 
        | Var (x:var)
        | Val (c:C)
        | Mul (c:C) (e:exp)
        | Zero (tl:list partype)
        | St (s: parstate) (t:partype)
        | Anni (s:sigma) (c:C) (t:partype) (tf:typeflag)
        | Trans (e:exp)
        | Tensor (e1:list exp)
        | Plus (e1:list exp)
        | Nor (e:exp)
        | Exp (e:exp)
        | Log (e:exp)
        | Lambda (x:var) (t:type) (e:exp)
        | Mu (x:var) (t:type) (e:exp)
        | If (e1:exp) (e2:exp) (e3:exp)
        | App (e1:exp) (e2:exp).


Fixpoint subst (e:exp) (x:var) (e1:exp) :=
  match e with Var y => if x =? y then e1 else Var y
             | Val c => Val c
             | Zero tl => Zero tl
             | St s t => St s t
             | Mul c ea => Mul c (subst ea x e1)
             | Anni s c t tf => Anni s c t tf
             | Trans ea => Trans (subst ea x e1)
             | Tensor ea => Tensor (List.map (fun e => subst e x e1) ea)
             | Plus ea => Plus (List.map (fun e => subst e x e1) ea)
             | Nor ea => Nor (subst ea x e1)
             | Exp ea => Exp (subst ea x e1)
             | Log ea => Log (subst ea x e1)
             | Lambda y t ea => if x =? y then Lambda y t ea else Lambda y t (subst ea x e1)
             | Mu y t ea => if x =? y then Mu y t ea else Mu y t (subst ea x e1)
             | If ea eb ec => If (subst ea x e1) (subst eb x e1) (subst ec x e1)
             | App ea eb => App (subst ea x e1) (subst eb x e1)
  end.

Fixpoint list_sub (s:list var) (b:var) :=
   match s with nil => nil
              | a::al => if a =? b then list_sub al b else a::list_sub al b
   end.

Fixpoint freeVars (e:exp) :=
  match e with Var y => [y]
             | Val c => []
             | Zero tl => []
             | St s t => []
             | Anni s c t tf => []
             | Mul c ea => freeVars ea
             | Trans ea => freeVars ea
             | Tensor ea => List.fold_right (fun e l => freeVars e ++ l) [] ea
             | Plus ea => List.fold_right (fun e l => freeVars e ++ l) [] ea
             | Nor ea => freeVars ea
             | Exp ea => freeVars ea
             | Log ea => freeVars ea
             | Lambda y t ea => list_sub (freeVars ea) y
             | Mu y t ea => list_sub (freeVars ea) y
             | If ea eb ec => freeVars ea ++ freeVars eb ++ freeVars ec
             | App ea eb => freeVars ea ++ freeVars eb
  end.

Fixpoint varCap (e:exp) (x:var) :=
  match e with Var y => False
             | Val c => False
             | Zero tl => False
             | St s t => False
             | Anni s c t tf => False
             | Mul c ea => varCap ea x
             | Trans ea => varCap ea x 
             | Tensor ea => List.fold_right (fun e l => varCap e x \/ l) False ea 
             | Plus ea => List.fold_right (fun e l => varCap e x \/ l) False ea 
             | Nor ea => varCap ea x 
             | Exp ea => varCap ea x 
             | Log ea => varCap ea x 
             | Lambda y t ea => if x =? y then True else varCap ea x 
             | Mu y t ea => if x =? y then True else varCap ea x 
             | If ea eb ec => varCap ea x \/ varCap eb x \/ varCap ec x
             | App ea eb => varCap ea x \/ varCap eb x 
  end.

Parameter I : exp.

Parameter find_n : exp -> nat.

Fixpoint eton (n:nat) (e:exp) :=
   match n with 0 => I
             | S m => App e (eton m e)
   end.

Fixpoint pow_exp' (n:nat) (e:exp) :=
    match n with 0 => nil
               | S m => (Mul (Cdiv (Copp Ci) (INR (fact(m)))) (eton m e))::pow_exp' m e
    end.
Definition pow_exp n e :=
   match pow_exp' n e with nil => I | l => Plus l end.

Fixpoint pow_log' (n:nat) (e:exp) :=
   match n with 0 => (e::((Mul (Copp C1) I)::nil))
              | S m => (Mul (Cdiv (Copp C1) (INR n)) (eton n (Plus (I::(Mul (Copp C1) e)::nil))))::(pow_log' m e)
   end.
Definition pow_log n e := Plus (pow_log' n e).


Inductive is_zero : exp -> Prop :=
  | single_zero : forall s t, allzero = snd s -> is_zero (St s t)
  | multi_zero : forall l, Forall (fun x => match x with St s t => allzero = snd s
                                                        | _ => False end) l -> is_zero (Tensor l).

Fixpoint zip (xs : list exp) (ys : list exp) : list exp :=
  match xs, ys with
  | x :: xs, y :: ys => (App x y) :: zip xs ys
  | _, _ => []
  end.

Inductive MergeTensor: list exp -> list partype -> Prop :=
  merge_tensor_empty : MergeTensor nil nil
  | merge_tensor_many_1 : forall l tl s t, MergeTensor l tl -> MergeTensor ((St s t)::l) (t::tl)
  | merge_tensor_many_2 : forall l tl t, MergeTensor l tl -> MergeTensor ((Zero t)::l) (t++tl).


Inductive equiv : exp -> exp -> Prop :=
  | plus_st: forall tl l, equiv (Plus ((Zero tl)::l)) (Plus l)
  | tensor_zero: forall l tl, (exists ta, In (Zero ta) l) -> MergeTensor l tl -> equiv (Tensor l) (Zero tl)
  | alpha_1 : forall x y t ea, List.In y (freeVars ea) -> varCap ea y 
         -> equiv (Lambda x t ea) (Lambda y t (subst ea x (Var y)))
  | alpha_2 : forall x y t ea, List.In y (freeVars ea) -> varCap ea y 
         -> equiv (Mu x t ea) (Mu y t (subst ea x (Var y)))
  | plus_exb_1: forall ea eb, equiv (App (Plus ea) eb) (Plus (List.map (fun x => App x eb) ea))
  | plus_exb_2: forall ea eb, equiv (App ea (Plus eb)) (Plus (List.map (fun x => App ea x) eb))
  | plus_tensor: forall ea eb, equiv (Tensor ((Plus ea)::eb)) (Plus (List.map (fun x => Tensor (x::eb)) ea))
(*  | plus_tensor_2: forall ea eb ec, equiv (Tensor ec (Plus ea eb)) (Plus (Tensor ec ea) (Tensor ec eb)) *)
  | trans_tensor: forall e, equiv (Trans (Tensor e)) (Tensor (List.map (fun x => Trans x) e))
  | trans_plus: forall e, equiv (Trans (Plus e)) (Plus (List.map (fun x => Trans x) e))
  | trans_app: forall ea eb, equiv (Trans (App ea eb)) (App (Trans eb) (Trans ea))
  | trans_mul: forall ea y t c, equiv (App ea (Trans (Lambda y t (Mul c (Var y))))) (Mul (Cconj c) ea)
  | trans_nor: forall ea, equiv (Trans (Nor ea)) (Nor (Trans ea))
  | tensor_app : forall el1 el2, length el1 = length el2 ->
             equiv (App (Tensor (el1)) (Tensor (el2))) (Tensor (zip el1 el2))
  | exp_appx: forall e, equiv (Exp e) (pow_exp (find_n e) e)
  | log_appx: forall e, equiv (Log e) (pow_log (find_n e) e)
  | equiv_self : forall e, equiv e e
  | equiv_trans: forall e1 e2 e3, equiv e1 e2 -> equiv e2 e3 -> equiv e1 e3.

Ltac ctx e1 e2 :=
  let H := fresh "HCtx" in
  assert (e1 = e2) as H by reflexivity.

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.
