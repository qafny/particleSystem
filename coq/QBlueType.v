(*  the rewrite rules and typing system of QBlue *)

Require Import List.
Import ListNotations.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.

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

    
Inductive rewrites : blueExp -> blueExp -> Prop :=
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
Inductive rewrites_recur :  blueExp -> blueExp -> Prop :=
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
Inductive typing : blueExp -> tau -> Prop :=
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


(* Check if expression e is canonical *)
(* Fixpoint is_canonical (f : bool) (e : H) : bool :=
  match e with
  | HAnni _ _ _ => true

  | HDag e' =>
      match e' with
      | HAnni _ _ _ => true
      | _ => false
      end

  | HTensor e1 e2 =>
      if f then
        is_canonical true e1 && is_canonical true e2
      else false

  | HApp e1 e2 =>
      if f then
        is_canonical true e1 && is_canonical true e2
      else false

  | HPlus e1 e2 =>
      is_canonical f e1 && is_canonical f e2
  end.*)

Definition ket_matches_iota (k : ket) (i : iota) : bool :=
    let '(_, particles) := k in
    Nat.eqb (length particles) (length i).
  
Definition is_type (tp : tau) (qphi : phi) : bool :=
    let '(_, i) := tp in
    forallb (fun k => ket_matches_iota k i) qphi.


(* Theorem: type soundness *)
Theorem type_progress: forall (e: H) (tp: tau) (qphi: phi), 
(typing e tp) -> (is_type tp qphi=true) -> (canonicalCheck false e) 
-> exists qphi', sem e qphi qphi'.
Proof.
Admitted.  

Theorem type_preservation: forall (e: H) (tp: tau) (qphi: phi) (qphi': phi), 
(typing e tp) -> (is_type tp qphi=true) -> (canonicalCheck false e) 
-> sem e qphi qphi' -> (is_type tp qphi'=true). 
Proof.
Admitted.
