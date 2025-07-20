(*  the rewrite rules and typing system of QBlue *)

Require Import List.
Import ListNotations.
Require Import QuantumLib.Complex.
Require Import QuantumLib.VectorStates.
Require Import QBlue.QBlueSyntax.

(*
(* To make sure all programs are in canonical forms
e.g., only the followings are allowed:
a, a+, (any e1) + (any e2),
(e1 e2)⊗e3, e1(e2⊗e3) *)
Inductive canonicalCheck : bool -> H -> Prop := 
  | canonicalCheckAnni: forall c s m f, canonicalCheck f (HAnni c s m)
  | canonicalCheckHDag: forall c s m f, canonicalCheck f (HDag (HAnni c s m)) 
  (* within dagger only HAnni is allowed. *)
  | canonicalCheckHTensor: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HTensor e1 e2)
  | canonicalCheckHPlus: forall e1 e2 f, canonicalCheck f e1 -> canonicalCheck f e2
    -> canonicalCheck false (HPlus e1 e2)
  | canonicalCheckHApp: forall e1 e2 f, canonicalCheck true e1 -> canonicalCheck true e2
    -> canonicalCheck f (HApp e1 e2).
    *)

Definition no_fem (t:iota) := forall e, In e t -> e <> Fem.

Inductive rewrites : iota -> blueExp -> blueExp -> Prop :=
(* (e1 + e2) e ≡ (e1 e) + (e2 e) *)
| R_App_Plus_L : forall t e1 e2 e,
    rewrites t (HApp (HPlus e1 e2) e)
             (HPlus (HApp e1 e) (HApp e2 e))

(* e (e1 + e2) ≡ (e e1) + (e e2) *)
| R_App_Plus_R : forall t e1 e2 e,
    rewrites t (HApp e (HPlus e1 e2))
             (HPlus (HApp e e1) (HApp e e2))

(* (e1 + e2) ⊗ e ≡ e1 ⊗ e + e2 ⊗ e *)
| R_Tensor_Plus_L : forall t e1 e2 e,
    rewrites t (HTensor (HPlus e1 e2) e)
             (HPlus (HTensor e1 e) (HTensor e2 e))

(* e ⊗ (e1 + e2) ≡ e ⊗ e1 + e ⊗ e2 *)
| R_Tensor_Plus_R : forall t e1 e2 e,
    rewrites t (HTensor e (HPlus e1 e2))
             (HPlus (HTensor e e1) (HTensor e e2))

(* (e1 + e2)+ ≡ e1+ + e2+ *)
| R_Dag_Plus : forall t e1 e2,
    rewrites t (HDag (HPlus e1 e2))
             (HPlus (HDag e1) (HDag e2))

(* (e1 ⊗ e2)+ ≡ e1+ ⊗ e2+ *)
| R_Dag_Tensor : forall t e1 e2,
    rewrites t (HDag (HTensor e1 e2))
             (HTensor (HDag e1) (HDag e2))

(* (e1 e2)† ≡ e2† e1† *)
| R_Dag_App : forall t e1 e2,
    rewrites t (HDag (HApp e1 e2))
             (HApp (HDag e2) (HDag e1))

(* (e+)+ ≡ e *)
| R_Double_Dag : forall t e,
    rewrites t (HDag (HDag e)) e

| R_ten: forall t e1 e2 e3 e4, no_fem t -> rewrites t (HApp (HTensor e1 e2) (HTensor e3 e4)) (HTensor (HApp e1 e3) (HApp e2 e4))

| R_dag_id : forall t, rewrites t (HDag HId) HId

| R_app_id_l : forall t e, rewrites t (HApp HId e) e

| R_app_id_r : forall t e, rewrites t (HApp e HId) e.


(* To allow multi-step rewrite *)
Inductive rewrites_recur :  iota -> blueExp -> blueExp -> Prop :=
| RS_Refl : forall t e, rewrites_recur t e e
| RS_Step : forall t e1 e2 e3,
    rewrites t e1 e2 ->
    rewrites_recur t e2 e3 ->
    rewrites_recur t e1 e3.
   
    
(* helper func for T-APP 
Definition uni_tp (zt1 zt2 : xi) : xi :=
    match  zt1, zt2 with
    | p, _ => p
    | _, p => p
    | _, _ => h
    end.


Definition uni_tp (zt1 zt2 : typeflag) : typeflag :=
    match  zt1, zt2 with
    | P, _ => P
    | _, P => P
    | _, _ => H
    end.
*)
(* Typing rules *)
Inductive typing : iota -> blueExp -> tauType -> Prop :=
| T_opF : typing ([Fem]) HAnni (P,[Fem])
| T_opB : forall m,
    typing ([Bos m]) HAnni (P,([Bos m]))

| T_ID : forall t, typing t HId (P,t)

| T_DAG : forall t e tp,
    typing t e tp ->
    typing t (HDag e) tp

| T_HER : forall t e,
    rewrites_recur t (HDag e) e ->
    typing t e (P,t) ->
    typing t e (H,t)

| T_TENSOR : forall  t1 t2 e e' zeta,
    typing t1 e (zeta, t1) ->
    typing t2 e' (zeta, t2) ->
    typing (t1++t2) (HTensor e e') (zeta, (t1++t2))

| T_PLUS : forall t e e' zeta,
    typing t e (zeta, t) ->
    typing t e' (zeta, t) ->
    typing t (HPlus e e') (zeta, t)

| T_App : forall t e e' zeta,
    typing t e (zeta, t) ->
    typing t e' (zeta, t) ->
    typing t (HApp e e') (zeta, t).


(* Check if expression e is canonical *)
Fixpoint canonical_next (e:blueExp) : bool :=
  match e with HTensor e1 e2 => (canonical_next e1) && (canonical_next e2)
             | HApp e1 e2 => (canonical_next e1) && (canonical_next e2)
             | HAnni => true
  | HDag e' =>
      match e' with
      | HAnni => true
      | _ => false
      end

  | HId => true

  | _ => false
  end.

 Fixpoint is_canonical (e : blueExp) : bool :=
  match e with
  | HPlus e1 e2 =>
      is_canonical e1 && is_canonical e2

  | _ => canonical_next e
  end.


Lemma dag_canonical : forall e1 t, exists e2, rewrites_recur t e1 e2 /\ is_canonical e2 = true.
Proof.
 induction e1; intros; simpl in *.
Admitted.

