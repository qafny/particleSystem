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

Definition update_0 (st: nat -> nat -> nat) (j:nat) (n:nat) :=
    fun i => if i =? 0 then update (st 0) j n else st i.

(*
Definition sub_1 (v:nat -> basisket) (j:nat) :=
   fun a => if a =? 0 then (Cmult (sqrt (INR ((snd (v 0%nat)) 0 j))) (fst (v 0)),update_0 (snd (v 0)) j ((snd (v 0) 0 j) -1)) else v a.

Definition add_1 (v:nat -> basisket) (j:nat) :=
   fun a => if a =? 0 then (Cmult (sqrt (INR ((snd (v 0%nat) 0 j) + 1))) (fst (v 0)),update_0 (snd (v 0)) j ((snd (v 0) 0 j) + 1)) else v a.


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
Definition cal_inner (nl:list partype) (s1:parstate) (s2:parstate) :=
   match s1 with Ket m p => cal_inner' m nl p s2 | Zero => C0 end.
*)
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
  | anni_0 : forall j c t tv v t', ((v 0)) 0 j = 0 -> sem (App (Anni j c t tv) (St (Ket c1 v) t')) (St Zero t').
  | anni_n : forall j c t tv v t', (snd (v 0)) 0 j > 0 -> sem (App (Anni j c t tv) (St (Ket c v) t')) (St (Ket 1 (sub_1 v j)) t')
  | crea_0 : forall j c t tv v t', (snd (v 0)) 0 j = (snd t) - 1 -> sem (App (Trans (Anni j c t tv)) (St (Ket 1 v) t')) (St Zero t')
  | crea_n : forall j c t tv v t', (snd (v 0)) 0 j < (snd t) - 1 
                 -> sem (App (Trans (Anni j c t tv)) (St (Ket 1 v) t')) (St (Ket 1 (add_1 v j)) t')
  | lambda_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb)
  | mu_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb) 
  | inner_rule : forall s s' nl nl', sem (App (Trans (St s nl)) (St s' nl')) (Val (cal_inner nl s s'))
  | nor_rule : forall s t, sem (Nor (St s t)) (Val (cal_inner t s s)).




