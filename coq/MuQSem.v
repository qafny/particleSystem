Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
Require Import MuQSyntax.

Local Open Scope nat_scope.

(* This document contains the semantics of MuQ, 
    which admits the style of the lambda-calculus substitution based semantics.
   The inductive relation sem take an MuQ exp and outputs another exp. *)

(*
Definition update_0 (st: nat -> nat -> nat) (j:nat) (n:nat) :=
    fun i => if i =? 0 then update (st 0) j n else st i.

Definition mut_state (size:nat) (s1 s2: spinbase) :=
   fun i => if i <? size then s1 i else s2 (i-size).

Fixpoint times_state_aux (i:nat) (size:nat) (m:nat) (lsize:nat) (c:C) (v:spinbase) (s:nat -> basisket) (acc:nat -> basisket) :=
  match m with 0 => acc
            | S j => update (times_state_aux i size j lsize c v s acc) (i*size + j) (Cmult c (fst (s j)), mut_state lsize v (snd (s j)))
  end.

Fixpoint times_state (m:nat) (m':nat) (lsize:nat) (s1 s2: nat -> basisket) :=
  match m with 0 => zerostate
           | S j => times_state_aux j m' m' lsize (fst (s1 j)) (snd (s1 j)) s2 (times_state j m' lsize s1 s2)
  end.

Definition put_join (size:nat) (sa sb: parstate) :=
  match sa with Zero => Zero
              | Ket m v =>
    match sb with Zero => Zero
                | Ket m' v' => Ket (m*m') (times_state m m' size v v')
    end
  end.

Definition put_plus (sa sb: parstate) :=
  match sa with Zero => Zero
              | Ket m v =>
    match sb with Zero => Zero
                | Ket m' v' => Ket (m+m') (fun i => if i <? m then v i else v' (i - m))
    end
  end.

Fixpoint cal_dot_aux (s1 s2:nat -> nat) (n:nat) :=
  match n with 0 => true
             | S m => if s1 m =? s2 m then cal_dot_aux s1 s2 m else false
  end.

Fixpoint cal_dot (s1 s2:spinbase) (nl:list partype) :=
  match nl with [] => true
             | ((n,m)::ml) => if cal_dot_aux (s1 (length ml)) (s2 (length ml)) n then cal_dot s1 s2 ml else false
  end.

Fixpoint cal_inner_aux' (m:nat) (nl: list partype ) (s2:basisket) (s1:nat -> basisket) :=
   match m with 0 => C0
              | S j =>  if cal_dot (snd s2) (snd (s1 j)) nl
                        then Cplus (Cmult (fst s2) (fst (s1 j))) (cal_inner_aux' j nl s2 s1)
                        else cal_inner_aux' j nl s2 s1
   end.
Definition cal_inner_aux (nl:list (nat*nat)) (s2:basisket) (s1:parstate) :=
   match s1 with Ket m p => cal_inner_aux' m nl s2 p | Zero => C0 end.

Fixpoint cal_inner' (m:nat) (nl:list partype) (s1:nat -> basisket) (s2:parstate) :=
   match m with 0 => C0
              | S j =>  Cplus (cal_inner_aux nl (s1 j) s2) (cal_inner' j nl s1 s2)
   end.
*)


Inductive OnlyState: exp -> Prop :=
  only_state : forall s t, OnlyState (St s t).

Inductive WFState' : nat -> list exp -> Prop :=
   well_form_empty: forall n, WFState' n nil
 | well_form_many : forall n x l, length x = n -> (Forall OnlyState x) -> WFState' n ((Tensor x)::l).
Definition WFState (el:list exp) :=
  match el with nil => True | (Tensor x::xl) => WFState' (length x) (Tensor x::xl) | _ => False end.

Inductive col_c : list exp -> C -> Prop :=
   col_empty : col_c nil C1
 | col_many : forall s t l c, col_c l c -> col_c ((St s t)::l) (Cmult c (fst s)).

Inductive col_mod : list exp -> R -> Prop :=
   col_mod_empty : col_mod nil (0:R)
 | col_mod_many : forall sl l c r, col_c sl c -> col_mod l r -> col_mod ((Tensor sl)::l) (Rplus ((Cmod c)^2) r).


Inductive cal_norm_aux (r:R) : list exp -> list exp -> Prop :=
   cal_aux_empty : cal_norm_aux r nil nil
 | cal_aux_many : forall s t l, cal_norm_aux r ((St s t)::l) ((St ((Cdiv (fst s) r),snd s) t)::l).


Inductive cal_norm (r:R) : list exp -> list exp -> Prop :=
   col_norm_empty : cal_norm r nil nil
 | col_norm_many : forall sl sl' l l', cal_norm_aux r sl sl' -> cal_norm r l l' -> cal_norm r ((Tensor sl)::l) ((Tensor sl')::l').

Fixpoint cal_ket (s1 s2:spinbase) (n:nat) :=
   match n with 0 => True
              | S m => (s1 m = s2 m) /\ cal_ket s1 s2 m
   end.

Inductive cal_tensor : list exp -> list exp -> Prop :=
     cal_ten_empty: cal_tensor nil nil
   | cal_ten_many: forall s1 t1 s2 t2 l1 l2, 
       cal_tensor l1 l2 -> cal_ket (snd s1) (snd s2) (fst t1) -> cal_tensor ((St s1 t1)::l1) ((St s2 t2)::l2).

Inductive cal_inner_ten : list exp -> list exp -> C -> Prop :=
   cal_inner_ten_rule: forall l1 l2 c1 c2, cal_tensor l1 l2 -> col_c l1 c1 -> col_c l2 c2 -> cal_inner_ten l1 l2 (Cmult (Cinv c1) c2).

Inductive cal_inner_aux : list exp -> list exp -> C -> Prop :=
    cal_inner_aux_empty: forall s, cal_inner_aux s nil C0
  | cal_inner_aux_many: forall s s1 l c ca, cal_inner_ten s s1 c -> cal_inner_aux s l ca -> cal_inner_aux s (Tensor s1::l) (Cplus c ca).

Inductive cal_inner : list exp -> list exp -> C -> Prop :=
    cal_inner_empty: forall xl, cal_inner nil xl C0
  | cal_inner_many: forall s l xl c ca, cal_inner_aux s l c -> cal_inner l xl ca -> cal_inner (Plus s::l) xl (Cplus c ca).


(*
Inductive resolve : exp -> nat * parstate -> Prop :=
  | zero_deal : forall t, resolve (St Zero t) (fst t, Zero)
  | st_deal : forall m v t, resolve (St (Ket m v) t) (fst t, Ket m v)
  | tensor_deal: forall ea eb sa sb, resolve ea sa -> resolve eb sb
                 -> resolve (Tensor ea eb) (fst sa + fst sb, put_join (fst sa) (snd sa) (snd sb))
  | resolve_plus: forall ea eb la lb, fst la = fst lb -> resolve ea la -> resolve eb lb
                 -> resolve (Plus ea eb) (fst la, put_plus (snd la) (snd lb)).
*)
Inductive sem : exp -> exp -> Prop :=
  | anni_0 : forall j c t tv v t', (snd v) j = 0 -> sem (App (Anni j c t tv) (St v t')) (Zero [t'])
  | anni_n : forall j c t tv v t', v j > 0 -> 
         sem (App (Anni j c t tv) (St (c,v) t')) (St ((Cmult (sqrt (INR (v j))) c), (update v j (v j - 1))) t')
  | crea_0 : forall j c c1 t tv v t', v j = (snd t) - 1 
                -> sem (App (Trans (Anni j c t tv)) (St (c1,v) t')) (Zero [t'])
  | crea_n : forall j c c1 t tv v t', v j < (snd t) - 1 
                 -> sem (App (Trans (Anni j c t tv)) (St (c1, v) t'))
                               (St ((Cmult (sqrt (INR (v j + 1))) c1), (update v j (v j + 1))) t')
  | lambda_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb)
  | mu_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb)
  | inner_rule : forall s s' c, cal_inner s s' c -> sem (App (Trans (Plus s)) (Plus s')) (Val c)
  | nor_rule : forall s c s', col_mod s c -> cal_norm c s s' -> sem (Nor (Plus s)) (Plus s').

