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

Fixpoint Cpow (c : C) (n : nat) : C :=
  match n with
  | O   => C1
  | S k => c * Cpow c k
  end.

Notation "c ^ n" := (Cpow c n) : C_scope.

(* nat: contex number, record occupied fermions
  iota: state type; blueExp: op; psi: input and output state (C amplitude, nat->nat site_id :  ) *)
Inductive blue_sem : nat -> iota -> blueExp -> psi -> psi -> Prop := 
 | s_id : forall n t s, blue_sem n t HId s s
 | f_anni_1: forall n s, anni_sem (snd s 0) = None -> blue_sem n ([Fem]) HAnni ([s]) (nil)
 | f_anni_2: forall n s c m, anni_sem (snd s 0) = Some (c,m) 
     -> blue_sem n ([Fem]) HAnni ([s]) ([(Cmult (C1 ^ n) (Cmult c (fst s)), (update (snd s) 0 m))]) 
 | f_crea_1: forall n s, create_sem 1 (snd s 0) = None -> blue_sem n ([Fem]) (HDag HAnni) ([s]) (nil)
 | f_crea_2: forall n s c m, create_sem 1 (snd s 0) = Some (c,m)
     -> blue_sem n ([Fem]) (HDag HAnni) ([s]) ([(Cmult (C1 ^ n) (Cmult c (fst s)), (update (snd s) 0 m))])
 | b_anni_1: forall n j s, anni_sem (snd s 0) = None -> blue_sem n ([Bos j]) HAnni ([s]) (nil)
 | b_anni_2: forall n j s c m, anni_sem (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) HAnni ([s]) ([(Cmult c (fst s), (update (snd s) 0 m))])
 | b_crea_1: forall n j s, create_sem j (snd s 0) = None -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) (nil)
 | b_crea_2: forall n j s c m, create_sem j (snd s 0) = Some (c,m)
               -> blue_sem n ([Bos j]) (HDag HAnni) ([s]) ([(Cmult c (fst s), (update (snd s) 0 m))])
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
      typing ia e (HER, ia) ->
      blueExp_Hermitian ia e ->
      interprete_herm ia e.

Lemma typing_sound_hermitian :
  forall ia e h,
    typing ia e h -> fst h = HER -> snd h = ia ->
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
Theorem type_right_matrix: forall ia e, typing ia e (HER, ia) -> rewrites_recur ia (HDag e) e.
Proof.
  intros ia e Htype.
  apply hermitian_rewrites.
Admitted.

(* The estimated state for HAnni 
g: context number to record the # of fermions; amp: amplitude; 
f: mapping to record the # of particles per site *)
Definition ket_minus_one_fem (g : nat) (amp : C) (f : basisKet) : list (C * basisKet) :=
  match anni_sem (f 0) with
  | None => []
  | Some (c, m') => [(Cmult (C1 ^ g) (Cmult c amp), update f 0 m')]
  end.

Fixpoint tysound_hanni_fem (g : nat) (s : psi) : psi := 
  match s with 
  | [] => []
  | k :: s' => ket_minus_one_fem g (fst k) (snd k) ++ (tysound_hanni_fem g s')
  end.

Definition ket_minus_one_bos (amp : C) (f : basisKet) : list (C * basisKet) :=
  match anni_sem (f 0) with
  | None => []
  | Some (c, m') => [(Cmult c amp, update f 0 m')]
  end.

Fixpoint tysound_hanni_bos (s : psi) : psi := 
  match s with 
  | [] => []
  | k :: s' => ket_minus_one_bos (fst k) (snd k) ++ (tysound_hanni_bos s')
  end.

Definition ket_plus_one_fem (g : nat) (amp : C) (f : basisKet) : list (C * basisKet) :=
  match create_sem 1 (f 0) with
  | None => []
  | Some (c, m') => [(Cmult (C1 ^ g) (Cmult c amp), update f 0 m')]
  end.

Fixpoint tysound_hdag_fem (g : nat) (s : psi) : psi := 
  match s with 
  | [] => []
  | k :: s' => ket_plus_one_fem g (fst k) (snd k) ++ (tysound_hdag_fem g s')
  end.

(* b: # of particles in one site should be <= b *)
Definition ket_plus_one_bos (b : nat) (amp : C) (f : basisKet) : list (C * basisKet) :=
  match create_sem b (f 0) with
  | None => []
  | Some (c, m') => [(Cmult c amp, update f 0 m')]
  end.

Fixpoint tysound_hdag_bos (b : nat) (s : psi) : psi := 
  match s with 
  | [] => []
  | k :: s' => ket_plus_one_bos b (fst k) (snd k) ++ (tysound_hdag_bos b s')
  end.


Lemma part_is_wfstate_fem: forall (a: (C * basisKet)) (s : list (C * basisKet)),
  WFState [Fem] (a :: s) -> WFState [Fem] s.
Proof.
  intros a s IH1 t IH2.
  apply IH1. right. easy.
Qed.

Lemma part_is_wfstate_bos: forall (a : C * basisKet) (s : list (C * basisKet)) (m : nat),
  WFState [Bos m] (a :: s) -> WFState [Bos m] s.
Proof.
  intros a s m IH1 t IH2.
  apply IH1. right. easy.
Qed.

Lemma fem_bound_ins: forall (a : C * basisKet) (s : list (C * basisKet)), 
  WFState [Fem] (a :: s) -> snd a 0 < 2.
Admitted.

Lemma fem_bound1: forall (a : C * basisKet) (c : C) (n0 : nat), 
  anni_sem (snd a 0) = Some (c, n0) -> n0 < 2.
Admitted.

Lemma fem_bound2: forall (a : C * basisKet) (c : C) (n0 : nat), 
  snd a 0 < 2 -> create_sem 1 (snd a 0) = Some (c, n0) -> n0 < 2.
Admitted.

  
(* ia: iota, state type; e: op; t: op type; n: context number for fermion; s: input state *)
Theorem can_type_soundness: forall ia e t n s, typing ia e t  -> is_canonical e = true -> WFState ia s 
  -> exists s', blue_sem n ia e s s' /\ WFState ia s'.
Proof. 
  intros ia e t n s Hty Hcan Hst. induction Hty.
  
  - (* 1. blue_sem n [Fem] HAnni s (tysound_hanni s) /\ WFState [Fem] (tysound_hanni s) *)  
    exists (tysound_hanni_fem n s). split.
    -- apply s_top. induction s as [|a s' IHs].
      --- simpl. constructor.
      --- simpl. constructor.
        + (* deal with a in a::s': blue_sem n [Fem] HAnni [a] (ket_minus_one_fem (fst a) (snd a)) *)
          unfold ket_minus_one_fem. destruct (anni_sem (snd a 0)) eqn:eq1.
          ++ (* Some (c, n0) *)
          destruct p as [c n0]. 
          apply f_anni_2. apply eq1.
          ++ (* None *)
          constructor. apply eq1.
        
        + (* deal with s' in a::s': forall_map (blue_sem n [Fem] HAnni) s' (tysound_hanni s') *)
          apply IHs. intros e IHe. (* intro var and hypo for WFState *)
          apply Hst. right. apply IHe.
    
    (* WFState [Fem] (tysound_hanni_fem s) *)
    -- induction s as [|a s' IH1].
      --- (* WFState [Fem] (tysound_hanni_fem n []) *)
        simpl. easy.
      --- (* WFState [Fem] (tysound_hanni_fem n (a :: s')) *)
        simpl. unfold WFState. 
        intros e IHe. (* introduce the var in the def of WState *) 
        apply in_app_or in IHe. destruct IHe as [IHe1 | IHe2]. (* break IH to 2 parts *)
        (* Goal: WFKet [Fem] (snd e) *)
        + (* IHe1: In e (ket_minus_one_fem n (fst a) (snd a)) *)
          unfold ket_minus_one_fem in IHe1. destruct (anni_sem (snd a 0)) eqn:eq1.
          ++ (* Some p *)
            destruct p as [c n0]. simpl in IHe1. destruct IHe1 as [IHe1_1 | IHe1_1].
            +++ (* ((C1 ^ n * (c * fst a))%C, update (snd a) 0 n0) = e *)
            destruct IHe1_1. simpl. (* replace (snd e) with update (snd a) 0 n0 *)
            constructor. (* get the 2 req for WFKet *)
              ++++ (* Goal: update (snd a) 0 n0 0 < 2 *)
                unfold update. simpl.
                (* n0 < 2 *)
                assert (In a (a :: s')) as G1. left. easy. apply Hst in G1. inv G1. (* get: snd a 0 < 2 *)
                unfold anni_sem in eq1. destruct (snd a 0) as [|n1] eqn:Eq2.
                +++++ easy.
                +++++ simpl in eq1. inv eq1. lia. 
                 
              ++++ (* Goal: WFKet [] (nleft (update (snd a) 0 n0) 1) *) constructor. 
                
            +++ (* e not in state *) inv IHe1_1. 
          ++ (* None *) easy.

        + (* IHe2: In e (tysound_hanni_fem n s') *)
          apply part_is_wfstate_fem in Hst.
          apply IH1 in Hst. apply Hst in IHe2. easy. 

  - (* 2. blue_sem n [Bos m] HAnni s (tysound_hanni s) /\ WFState [Bos m] (tysound_hanni s) *)  
    exists (tysound_hanni_bos s). split.
    -- apply s_top. induction s as [|a s' IHs].
      --- simpl. constructor.
      --- simpl. constructor.
        + unfold ket_minus_one_bos. destruct (anni_sem (snd a 0)) eqn:eq1.
          ++ (* Some (c, n0) *)
          destruct p as [c n0]. 
          apply b_anni_2. apply eq1.
          ++ (* None *)
          constructor. apply eq1.
        
        + apply IHs. intros e IHe. (* intro var and hypo for WFState *)
          apply Hst. right. apply IHe.
    
    (* WFState [Bos m] (tysound_hanni_bos s) *)
    -- induction s as [|a s' IH1].
      --- simpl. easy.
      --- simpl. unfold WFState. 
        intros e IHe. (* introduce the var in the def of WState *) 
        apply in_app_or in IHe. destruct IHe as [IHe1 | IHe2]. (* break IH to 2 parts *)
        (* Goal: WFKet [Fem] (snd e) *)
        + (* IHe1: In e (ket_minus_one_bos n (fst a) (snd a)) *)
          unfold ket_minus_one_bos in IHe1. destruct (anni_sem (snd a 0)) eqn:eq1.
          ++ (* Some p *)
            destruct p as [c n0]. simpl in IHe1. destruct IHe1 as [IHe1_1 | IHe1_1].
            +++ (* ((C1 ^ n * (c * fst a))%C, update (snd a) 0 n0) = e *)
            destruct IHe1_1. simpl. (* replace (snd e) with update (snd a) 0 n0 *)
            constructor. (* get the 2 req for WFKet *)
              ++++ (* Goal: update (snd a) 0 n0 0 < 2 *)
                unfold update. simpl.
                (* n0 < 2 *)
                assert (In a (a :: s')) as G1. left. easy. apply Hst in G1. inv G1. (* get: snd a 0 < 2 *)
                unfold anni_sem in eq1. destruct (snd a 0) as [|n1] eqn:Eq2.
                +++++ easy.
                +++++ simpl in eq1. inv eq1. lia. 
                 
              ++++ (* Goal: WFKet [] (nleft (update (snd a) 0 n0) 1) *) constructor. 
                
            +++ (* e not in state *) inv IHe1_1. 
          ++ (* None *) easy.

        + (* IHe2: In e (tysound_hanni_bos n s') *)  
        apply part_is_wfstate_bos in Hst.
        apply IH1 in Hst. apply Hst in IHe2. easy.
        
  - (* 3. blue_sem n t HId s s' /\ WFState t s' *)
    exists s. split. apply s_id. try easy.

  - (* 4. blue_sem n t (HDag e) s s' /\ WFState t s' *)
    simpl in Hcan. destruct e eqn : Eqcan.
    (* pick HDag HAnni with Hcan *)
    -- easy.
    -- (* blue_sem n t (HDag HAnni) s s' /\ WFState t s' *)
      (* pick t to be [Fem] or [Bos m] *)
      inv Hty. 
      --- (* blue_sem n [Fem] (HDag HAnni) s s' /\ WFState [Fem] s' *)  
        exists (tysound_hdag_fem n s). split.
        ---- apply s_top. induction s as [|a s' IHs].
          ----- simpl. constructor.
          ----- simpl. constructor.
            + unfold ket_plus_one_fem. destruct (create_sem 1 (snd a 0)) eqn:eq1.
              ++ destruct p as [c n0]. 
              apply f_crea_2. apply eq1.
              ++ constructor. apply eq1.
            + apply IHs.
              ++ admit.
              ++ apply part_is_wfstate_fem in Hst. easy.
      
        ---- (* WFState [Fem] (tysound_hdag_fem n s) *)
          induction s as [| a s' IH1].
          ----- simpl. easy.
          ----- simpl. unfold WFState.
            intros e IHe. apply in_app_or in IHe. destruct IHe.
            + (* H: In e (ket_plus_one_fem n (fst a) (snd a)). Goal: WFKet [Fem] (snd e) *)
              unfold ket_plus_one_fem in H.
              destruct (create_sem 1 (snd a 0)) eqn:eq1.
              ++ destruct p as [c n0]. simpl in H. destruct H as [H1 | H1].
                +++ destruct H1. simpl.
                    constructor.
                    ++++ unfold update. simpl. 
                      apply fem_bound_ins in Hst. 
                      apply fem_bound2 in eq1. easy. easy. 
                    ++++ constructor. 
                +++ easy. 
              ++ easy.  

            + (* H: In e (tysound_hdag_fem n s'). Goal: WFKet [Fem] (snd e) *)
              apply part_is_wfstate_fem in Hst. apply IH1 in Hst.
              ++ apply Hst in H. easy.
              ++ admit.
     
      --- (* blue_sem n [Bos m] (HDag HAnni) s s' /\ WFState [Bos m] s' *) 
        admit.
      --- (* blue_sem n t (HDag HAnni) s s' /\ WFState t s' *) 
        inv H. inv H1.
    -- easy.
    -- easy.
    -- easy.
    -- easy.
  
 
    

Admitted. 


Theorem type_soundness: forall ia e t n s, typing ia e t -> WFState ia s -> exists s',
  blue_sem n ia e s s' /\ WFState ia s'.
Proof. 
  intros ia e t n s Hty Hst.
  specialize (dag_canonical e ia) as G1.
  destruct G1. destruct H.
Admitted.
