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
Definition create_sem (m b : nat) : option (C * nat) :=
  if b <? m then Some (RtoC (sqrt (INR (b+1))), Nat.add b 1) else None.

(* annilator: a(m) |b> = sqrt(b) |b-1> *)
Definition anni_sem (b:nat) : option (C * nat) :=
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


(* nat: contex number, record occupied fermions
  iota: state type; blueExp: op; psi: input and output state (C amplitude, nat->nat site_id :  ) *)
Inductive blue_sem : nat -> iota -> blueExp -> psi -> psi -> Prop := 
 | s_id : forall n t s, blue_sem n t HId s s
 | f_anni_1: forall n s, anni_sem (snd s 0) = None -> blue_sem n ([Fem]) HAnni ([s]) (nil)
 | f_anni_2: forall n s c m, anni_sem (snd s 0) = Some (c,m) 
     -> blue_sem n ([Fem]) HAnni ([s]) ([(fst s, (update (snd s) 0 m))]) (* fst s should be (fst s)*c? *)
 | f_crea_1: forall n s, create_sem 1 (snd s 0) = None -> blue_sem n ([Fem]) (HDag HAnni) ([s]) (nil)
 | f_crea_2: forall n s c m, create_sem 1 (snd s 0) = Some (c,m)
               -> blue_sem n ([Fem]) (HDag HAnni) ([s]) ([(fst s, (update (snd s) 0 m))])
 | b_anni_1: forall n j s, anni_sem (snd s 0) = None -> blue_sem n ([Bos j]) HAnni ([s]) (nil)
 | b_anni_2: forall n j s c m, anni_sem (snd s 0) = Some (c,m)
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

(*  *)                 
Inductive WFKet : iota -> basisKet -> Prop := 
 | WFEmpty : forall s, WFKet nil s
 (* xl is the state of right part of s *)
 | WFManyF : forall xl s, s 0 < 2 -> WFKet xl (nleft s 1) -> WFKet (Fem::xl) s
 | WFManyB : forall m xl s, s 0 < m -> WFKet xl (nleft s 1) -> WFKet (Bos m::xl) s.


Definition WFState (t:iota) (s:psi) := forall e, In e s -> WFKet t (snd e).


(* Denote the blueExp as Matrix form *)
Fixpoint blueExp_dim (e : blueExp) : nat :=
  match e with
  | HId => 2
  | HAnni => 2
  | HPlus e1 e2 => blueExp_dim e1
  | HTensor e1 e2 => (blueExp_dim e1) * (blueExp_dim e2)
  | HApp e1 e2 => blueExp_dim e1
  | HDag e1 => blueExp_dim e1
  end.

(* Modify Mmult for the exceptional case of wrong dimension *)
Definition Mmult_tmp {m1 m2 n1 n2 : nat} (A : Matrix m1 m2) (B : Matrix n1 n2) : Matrix m1 n2 :=
  if Nat.eqb n1 m2 then Mmult A B
  else I m1. (* Not sure how to return erronic case. Zero has been overridn by MuQ files. *) 

Fixpoint blueExp_denote (e : blueExp) : Square (blueExp_dim e) :=
  match e with
  | HId => I 2
  | HAnni => fun i j =>
    match (i, j) with
    | (0, 1) => C1
    | _ => C0
    end
  | HPlus e1 e2 => Mplus (blueExp_denote e1) (blueExp_denote e2)
  | HTensor e1 e2 => kron (blueExp_denote e1) (blueExp_denote e2)
  | HApp e1 e2 => Mmult_tmp (blueExp_denote e1) (blueExp_denote e2)
  | HDag e1 => adjoint (blueExp_denote e1)
  end.

Definition Hermitian {n} (A : Square n) : Prop := mat_equiv (adjoint A) A.

Definition blueExp_Hermitian (ia : iota) (e : blueExp) : Prop :=
  Hermitian (blueExp_denote e).


Inductive interprete_herm : iota -> blueExp -> Prop :=
  | R_blueExp_Hermitian : forall ia e,
      typing ia e (H, ia) ->
      blueExp_Hermitian ia e ->
      interprete_herm ia e.

Lemma typing_sound_hermitian :
  forall ia e h,
    typing ia e h -> fst h = H -> snd h = ia ->
    blueExp_Hermitian ia e.
Proof.
intros ia e h Hypo.
induction e.
Admitted.


Lemma hermitian_rewrites :
  forall ia e,
    blueExp_Hermitian ia e ->
    rewrites_recur ia (HDag e) e.
Proof.
  intros ia e Hypo.
  unfold blueExp_Hermitian in Hypo.
  unfold Hermitian in Hypo.
  destruct e eqn:E. 
Admitted.


(* Theorem: type soundness *)
Theorem type_right_matrix: forall ia e, typing ia e (H, ia) ->  rewrites_recur ia (HDag e) e.
Proof.
  intros ia e Htype.
  apply hermitian_rewrites.
Admitted.

(* The estimated state for HAnni *)
Definition ket_minus_one (amp : C) (f : basisKet) : list (C * basisKet) :=
  match anni_sem (f 0) with
  | None => []
  | Some (c, m') => [(Cmult c amp, update f 0 m')]
  end.

Fixpoint tysound_hanni (s : psi) : psi := 
  match s with 
  | [] => []
  | k :: s' => ket_minus_one (fst k) (snd k) ++ (tysound_hanni s')
  end.


(* ia: iota, state type; e: op; t: op type; n: context number for fermion; s: input state *)
Theorem can_type_soundness: forall ia e t n s, typing ia e t  -> is_canonical e = true -> WFState ia s -> exists s',
  blue_sem n ia e s s' /\ WFState ia s'.
Proof. 
  intros ia e t n s Hty Hcan Hst. induction Hty.
  (* T_opF *)
  (* - remember (tysound_hanni s) as s1. *)
  - exists (tysound_hanni s).
    split. apply s_top.
    induction s. simpl in *. constructor. simpl in *. constructor.
    unfold ket_minus_one.
    destruct (anni_sem (snd a 0)) eqn:eq1. destruct p; simpl in *.
    assert (In a (a :: s)) as G1. left. easy.
    apply Hst in G1. inv G1.
    specialize (Hst a).
    assert ((c * fst a)%C = fst a).
    unfold anni_sem in *. destruct (snd a 0). simpl in *. easy. simpl in *. destruct n1.
    simpl in *. inv eq1. rewrite sqrt_1. lca.
    lia. rewrite H. apply f_anni_2 with (c := c); try easy.
    apply f_anni_1. easy. apply IHs.
    unfold WFState in *. intros. apply Hst. simpl. right. easy.
    induction s. simpl in *. easy.
    simpl in *. unfold WFState. intros. apply in_app_or in H. destruct H.
    constructor.
    unfold ket_minus_one in *. 
    destruct (anni_sem (snd a 0)) eqn:eq1. destruct p. simpl in *. inv H; try easy.
    simpl in *. rewrite update_index_eq.
    unfold anni_sem in eq1. destruct (snd a 0) eqn:eq2. simpl in *. easy. simpl in *. destruct n1. inv eq1. lia.
    inv eq1.
    assert (In a (a :: s)) as G1. left. easy.
    apply Hst in G1. inv G1. rewrite eq2 in H0. lia. easy.
    constructor.
    assert (WFState [Fem] s).
    unfold WFState. intros. apply Hst. right. easy.
    apply IHs in H0. apply H0 in H. easy.
  - admit.  
  - exists s. split. apply s_id. try easy.
 
Admitted.

Theorem type_soundness: forall ia e t n s, typing ia e t -> WFState ia s -> exists s',
  blue_sem n ia e s s' /\ WFState ia s'.
Proof. 
  intros ia e t n s Hty Hst.
  specialize (dag_canonical e ia) as G1.
  destruct G1. destruct H.
Admitted.
