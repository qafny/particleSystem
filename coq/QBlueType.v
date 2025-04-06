(*  the rewrite rules and typing system of QBlue *)

Require Import List.
Import ListNotations.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.


Inductive rewrites : H -> H -> Prop :=
(* (e1 + e2) e ≡ (e1 e) + (e2 e) *)
| R_App_Plus_L : forall e1 e2 e,
    rewrites (HApp (HPlus e1 e2) e)
             (HPlus (HApp e1 e) (HApp e2 e))

(* e (e1 + e2) ≡ (e e1) + (e e2) *)
| R_App_Plus_R : forall e1 e2 e,
    rewrites (HApp e (HPlus e1 e2))
             (HPlus (HApp e e1) (HApp e e2))

(* (e1 + e2) ⊗ e ≡ e1 ⊗ e + e2 ⊗ e *)
| R_Tensor_Plus_L : forall e1 e2 e,
    rewrites (HTensor (HPlus e1 e2) e)
             (HPlus (HTensor e1 e) (HTensor e2 e))

(* e ⊗ (e1 + e2) ≡ e ⊗ e1 + e ⊗ e2 *)
| R_Tensor_Plus_R : forall e1 e2 e,
    rewrites (HTensor e (HPlus e1 e2))
             (HPlus (HTensor e e1) (HTensor e e2))

(* (e1 + e2)+ ≡ e1+ + e2+ *)
| R_Dag_Plus : forall e1 e2,
    rewrites (HDag (HPlus e1 e2))
             (HPlus (HDag e1) (HDag e2))

(* (e1 ⊗ e2)+ ≡ e1+ ⊗ e2+ *)
| R_Dag_Tensor : forall e1 e2,
    rewrites (HDag (HTensor e1 e2))
             (HTensor (HDag e1) (HDag e2))

(* (e1 e2)† ≡ e2† e1† *)
| R_Dag_App : forall e1 e2,
    rewrites (HDag (HApp e1 e2))
             (HApp (HDag e2) (HDag e1))

(* (e+)+ ≡ e *)
| R_Double_Dag : forall e,
    rewrites (HDag (HDag e)) e.


(* To allow multi-step rewrite *)
Inductive rewrites_recur : H -> H -> Prop :=
| RS_Refl : forall e, rewrites_recur e e
| RS_Step : forall e1 e2 e3,
    rewrites e1 e2 ->
    rewrites_recur e2 e3 ->
    rewrites_recur e1 e3.
   
    
(* helper func for T-APP *)
Definition uni_tp (zt1 zt2 : xi) : xi :=
    match  zt1, zt2 with
    | p, _ => p
    | _, p => p
    | _, _ => h
    end.


(* Typing rules *)
Inductive typing : H -> tau -> Prop :=
| T_PAR : forall e e' tp,
    rewrites_recur e e' ->
    typing e' tp ->
    typing e tp

| T_OP : forall z m,
    typing (HAnni z p m) (p, [m])

| T_DAG : forall e tp,
    typing e tp ->
    typing (HDag e) tp

| T_TENSOR : forall e e' zeta l l',
    typing e (zeta, l) ->
    typing e' (zeta, l') ->
    typing (HTensor e e') (zeta, (l ++ l'))

| T_PLUS : forall e e' tp,
    typing e tp ->
    typing e' tp ->
    typing (HPlus e e') tp

| T_APP : forall e e' zeta zeta' l,
    typing e (zeta, l) ->
    typing e' (zeta', l) ->
    typing (HApp e e') (uni_tp zeta zeta', l)

| T_HER : forall e l,
    typing e (p, l) ->
    rewrites_recur (HDag e) e ->
    typing e (h, l).

