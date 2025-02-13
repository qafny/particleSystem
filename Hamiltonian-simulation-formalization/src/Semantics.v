(***************************************************************************************)
(**                                    Semantics.v                                    **)
(**                                                                                   **)
(** Defining the semantics of Hamiltonians and Hamiltonian programs; i.e., the effect **)
(** they have on quantum states. Also defining the interpretation of symbolic         **)
(** Hamiltonians into matrices. The main theorem of this project is located at the    **)
(** bottom of this file.                                                              **)
(**                                                                                   **)
(***************************************************************************************)

Require Import HSF_Syntax.
Require Import MatrixExponential.
Require Import Diagonalization.
Require Import String.
Require Import PauliRotations.
Require Import Lra.
Open Scope matrix_scope.
Open Scope list_scope.


(********************************************)
(** Hamiltonian Interpretation Definitions **)
(********************************************)

(* Dimensionality of Hilbert space for Hamiltonian program *)
Definition count_sites (prog : H_Program) := List.length (prog.(Decls)).
Definition dims (P : H_Program) : nat := 2 ^ (count_sites P).

Fixpoint sem_HScalar (sc : HScalar) : R :=
    match sc with
    | HScAdd s1 s2 => (sem_HScalar s1) + (sem_HScalar s2)
    | HScMult s1 s2 => (sem_HScalar s1) * (sem_HScalar s2)
    | HScSub s1 s2 => (sem_HScalar s1) - (sem_HScalar s2)
    | HScDiv s1 s2 => (sem_HScalar s1) / (sem_HScalar s2)
    | HScExp s => exp (sem_HScalar s)
    | HScCos s => cos (sem_HScalar s)
    | HScSin s => sin (sem_HScalar s)
    | HScReal v s => v
    end.

Fixpoint declsToMats (decls : list string) (label : string) (p : Pauli) : list (Square 2) :=
  match decls with
  | [] => []
  | d :: decls' =>
    (if String.eqb d label then PauliToMatrix p else I 2) :: (declsToMats decls' label p)
  end.

Definition interpret_HPauli_helper (decls : list string) (label : string) (p : Pauli) :=
  big_kron (declsToMats decls label p).

Fixpoint In_bool (x : string) (L : list string) : bool :=
  match L with
  | [] => false
  | y :: L' => orb (String.eqb x y) (In_bool x L')
  end.

Definition interpret_HPauli {n : nat} (decls : list string) (p : HPauli)
  : option (Square n) :=
  match p with HIdOp label pauli =>
               if In_bool label decls
               then Some (interpret_HPauli_helper decls label pauli)
               else None
  end.

(* Alternative implementation of interpret_HPauli *)
(* The above one is cleaner, but we also need this one for Trotterization *)
Fixpoint find_qubit (decls : list string) (label : string) : option nat :=
  match decls with
  | [] => None
  | head :: tail =>
      if String.eqb head label
      then
        Some O
      else
        match find_qubit tail label with
        | Some loc => Some (S loc)
        | None => None
        end
  end.

Definition interpret_HPauli' (decls : list string) (p : HPauli)
  : option (Square (2 ^ List.length decls)) :=
  let num_qubits := List.length decls in
  match p with HIdOp label pauli =>
    match find_qubit decls label with
      | Some loc => Some (padIs num_qubits (PauliToMatrix pauli) loc)
      | None => None
    end               
  end.

Lemma interpret_HPauli'_correct :
  forall decls hp,
    interpret_HPauli' decls hp = interpret_HPauli decls hp.
Proof.
  Admitted.

Fixpoint interpret_HPaulis {n : nat} (decls : list string) (ps : list HPauli)
        : option (Square n) :=
    match ps with
    | head :: tail =>
        match (interpret_HPauli decls head, interpret_HPaulis decls tail) with
        | (Some m1, Some m2) => Some (Mmult m1 m2)
        | _ => None
        end
    | [] => Some (I n)
    end.

Definition interpret_TIH_Term {n : nat} (decls : list string) (s : TIH_Term)
        : option (Square n) :=
    let sc_v := sem_HScalar s.(hScale) in
    match interpret_HPaulis decls s.(hPaulis) with
    | Some pauli_v => Some (scale sc_v pauli_v)
    | None => None
    end.

Fixpoint interpret_TIH_Terms {n : nat} (decls : list string) (ss : list TIH_Term)
        : option (Square n) :=
    match ss with
    | head :: tail =>
        match (interpret_TIH_Term decls head, interpret_TIH_Terms decls tail) with
        | (Some m1, Some m2) => Some (Mplus m1 m2)
        | _ => None
        end
    | [] => Some Zero
    end.

(* Main interpretation function:
   Converts a HSF term into a Hamiltonian operator (an n x n matrix) *)
Definition interpret_term (prog : H_Program) (term : HSF_Term) : option (Square (dims prog)) :=
    interpret_TIH_Terms prog.(Decls) term.(Hamiltonian).



(***************************)
(** Semantics Definitions **)
(***************************)

(* Relational definition of Hamiltonian semantics *)
Definition sem_term {n : nat} (P : H_Program) (T : HSF_Term) (S : Square n) : Prop :=
    match interpret_term P T with
    | Some H =>
        let dt := sem_HScalar T.(Duration) in
        dims P = n /\ matrix_exponential (scale (-Ci * dt * one_over_h_bar) H) S (* e^{-iHt} =? S *)
    | None => False
    end.

(* Lists without duplicates *)
Inductive NoDup {A : Type} : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

(* Definition of a valid program *)
Definition program_valid (P : H_Program) : Prop :=
  (List.length (Decls P) > 0)%nat /\ NoDup (Decls P) /\
  forall (t : HSF_Term), In t (Terms P) -> In (TermId t) (Decls P).

(* Inductive definition for semantics of programs *)
Inductive sem_program {n : nat} : H_Program -> Square n -> Prop :=
  | sem_program_nil (D : list string)
                    (Hvalid : program_valid (makeHProg D []))
                    (Hdims : dims (makeHProg D []) = n) :
      sem_program (makeHProg D []) (I n)
  | sem_program_cons (D : list string) (t : HSF_Term) (T : list HSF_Term) (St SP : Square n)
                     (Ht : sem_term (makeHProg D T) t St)
                     (HP : sem_program (makeHProg D T) SP)
                     (Hvalid : program_valid (makeHProg D (t :: T)))
                     (Hdims : dims (makeHProg D (t :: T)) = n) :
      sem_program (makeHProg D (t :: T)) (St × SP)
.

Definition ham_commute (P : H_Program) (T1 T2 : HSF_Term) : Prop :=
    match (interpret_term P T1, interpret_term P T2) with
    | (Some H1, Some H2) => Mat_commute H1 H2
    | _ => False
    end.



(****************************************)
(** Lemmas about term/program validity **)
(****************************************)

Lemma semantics_implies_program_valid {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> program_valid P.
Proof.
  intros P S HS. inversion HS; subst.
  - destruct Hvalid as [Hlen [Hdup Hin]]. split; simpl in *.
    + assumption.
    + split; assumption.
  - destruct Hvalid as [Hlen [Hdup Hin]]. split; simpl in *.
    + assumption.
    + split; assumption.
Qed.    

Lemma term_removal_valid : forall P t T,
    program_valid P -> Terms P = t :: T -> program_valid (makeHProg (Decls P) T).
Proof.
  intros P t T HP HT. inversion HP. inversion H0. clear HP H0. split.
  - simpl. assumption.
  - split.
    + simpl. assumption.
    + simpl. intros t' Ht'. apply H2. rewrite HT. right. auto.
Qed.

Lemma no_terms_valid : forall (P : H_Program),
    program_valid P -> program_valid (makeHProg (Decls P) []).
Proof.
  intros P HP. destruct HP as [H1 [H2 H3]]. split; simpl; try auto.
  split; simpl; try auto.
  intros t Ht. contradiction.
Qed.

Lemma semantics_implies_no_terms_valid {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> program_valid (makeHProg (Decls P) []).
Proof.
  intros P S HP. apply no_terms_valid.
  remember (semantics_implies_program_valid P S HP) as goal.
  apply goal.
Qed.

Lemma extract_dims {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> dims P = n.
Proof.
  intros P S HP. inversion HP; subst; auto.
Qed.




(*************************************************************)
(** Lemmas about the well-formedness of term interpretation **)
(**   (i.e., interpret_term returns a well-formed matrix)   **)
(*************************************************************)

Lemma declsToMat_pauli_or_I : forall x d l p,
    In x (declsToMats d l p) -> x = PauliToMatrix p \/ x = I 2.
Proof.
  intros x d. generalize dependent x. induction d as [|y d'].
  - intros. contradiction.
  - intros. apply in_inv in H. destruct H.
    + destruct (y =? l)%string.
      * left. auto.
      * right. auto. 
    + apply IHd' in H. assumption. 
Qed.

Lemma interpret_HPauli_helper_WF :
  forall (decls : list string) (label : string) (p : Pauli),
    WF_Matrix (interpret_HPauli_helper decls label p).
Proof.
  intros.
  unfold interpret_HPauli_helper.
  destruct decls. apply WF_I.
  apply WF_big_kron with (I 2).
  intros i. destruct (blt_reflect i (List.length (declsToMats (s :: decls) label p))). 
  - eapply nth_In in l. apply declsToMat_pauli_or_I in l.
    destruct l.
    + rewrite H. apply PauliToMatrix_WF.
    + rewrite H. apply WF_I.
  - apply Nat.nlt_ge in n.
    eapply nth_overflow in n.
    rewrite n. apply WF_I.
Qed.

Lemma interpret_HPauli_WF :
  forall (decls : list string) (p : HPauli) (M : Square (2 ^ List.length decls)),
    interpret_HPauli decls p = Some M -> WF_Matrix M.
Proof.
  intros. destruct p eqn:Ep. unfold interpret_HPauli in H.
  destruct (In_bool loc decls) eqn:Ein; try discriminate.
  inversion H. clear H.
  assert (Hsize_eq : forall d l p', List.length d = List.length (declsToMats d l p')). {
    intros d. induction d as [|x d'].
    - intros. auto.
    - intros. simpl. apply f_equal. apply IHd'.
  }
  assert (Hdecls_length : (0 < List.length decls)%nat). {
    clear Hsize_eq H1 Ep p0 M p. apply neq_0_lt. intros contra.
    induction decls; discriminate.
  } 
  assert (Hsize_eq2 :
             (2^List.length decls = 2^List.length (declsToMats decls loc p0))%nat). {
    remember (Hsize_eq decls loc p0) as E. rewrite E.
    apply Nat.pow_inj_l with (List.length decls); auto.
    intros contra. apply lt_0_neq in Hdecls_length. symmetry in contra. contradiction.
  }
  unfold WF_Matrix. rewrite Hsize_eq2.
  apply interpret_HPauli_helper_WF.
Qed.

Lemma interpret_HPaulis_WF :
  forall (decls : list string) (ps : list HPauli) (M : Square (2 ^ List.length decls)),
    interpret_HPaulis decls ps = Some M -> WF_Matrix M.
Proof.
  intros decls ps. generalize dependent decls.
  induction ps as [|p ps']; intros.
  - inversion H. apply WF_I.
  - inversion H.
    destruct (interpret_HPauli decls p) eqn:E1; try discriminate.
    destruct (interpret_HPaulis decls ps') eqn:E2; try discriminate.
    inversion H1. apply WF_mult.
    + eapply interpret_HPauli_WF. apply E1.
    + eapply IHps'. apply E2.
Qed.

Lemma interpret_TIH_Term_WF :
  forall (decls : list string) (s : TIH_Term) (M : Square (2 ^ List.length decls)),
    interpret_TIH_Term decls s = Some M -> WF_Matrix M.
Proof.
  intros. unfold interpret_TIH_Term in H.
  destruct (interpret_HPaulis decls (hPaulis s)) eqn:E; try discriminate.
  inversion H.
  apply interpret_HPaulis_WF in E.
  apply WF_scale. assumption.
Qed.

Lemma interpret_TIH_Terms_WF : 
  forall (decls : list string) (ss : list TIH_Term) (M : Square (2 ^ List.length decls)),
    interpret_TIH_Terms decls ss = Some M -> WF_Matrix M.
Proof.
  intros decls ss. generalize dependent decls. induction ss as [|t T].
  - intros. inversion H. apply WF_Zero.
  - intros. inversion H. destruct (interpret_TIH_Term decls t) eqn:E1.
    + destruct (interpret_TIH_Terms decls T) eqn:E2.
      * apply IHT in E2. inversion H1. apply WF_plus.
        -- eapply interpret_TIH_Term_WF. apply E1.
        -- assumption.
      * discriminate.
    + discriminate.
Qed. 

(* Main lemma showing interpretation well-formedness *)
Theorem interpret_term_WF :
  forall (P : H_Program) (T : HSF_Term) (M : Square (dims P)),
    interpret_term P T = Some M -> WF_Matrix M.
Proof.
  intros P T M Hit.
  apply interpret_TIH_Terms_WF with (ss := Hamiltonian T) (decls := Decls P).
  unfold dims in M. unfold count_sites in M.
  unfold interpret_term in Hit. assumption.
Qed.




(*********************************************************)
(** Lemmas showing that Hamiltonian terms are Hermitian **)
(**  (i.e., interpret_term returns a Hermitian matrix)  **)
(*********************************************************)

Lemma interpret_HPauli_helper_herm :
  forall (decls : list string) (label : string) (p : Pauli),
    Herm (interpret_HPauli_helper decls label p).
Proof. 
  intros.
  unfold interpret_HPauli_helper.
  destruct decls. apply herm_I.
  apply herm_big_kron.
  rewrite Forall_forall. intros A H. apply declsToMat_pauli_or_I in H.
  destruct H; subst.
  - apply PauliToMatrix_herm.
  - apply herm_I.
Qed.  

Lemma interpret_HPauli_herm :
  forall (decls : list string) (p : HPauli) (M : Square (2 ^ List.length decls)),
    interpret_HPauli decls p = Some M -> Herm M.
Proof.
  intros. destruct p eqn:Ep. unfold interpret_HPauli in H.
  destruct (In_bool loc decls) eqn:Ein; try discriminate.
  inversion H. 
  apply interpret_HPauli_helper_herm.
Qed.

(* Last remaining lemma about semantics; tricky because HPauli terms are the kronecker
   product of lists of matrices *)
Lemma HPauli_terms_commute {n : nat} :
  forall (decls : list string) (p : HPauli) (ps : list HPauli) (M1 M2 : Square n),
    interpret_HPauli decls p = Some M1 ->
    interpret_HPaulis decls ps = Some M2 ->
    Mat_commute M1 M2.
Proof. Admitted.
(* This will likely require changing interpret_HPauli to ensure that no site receives more 
   than one Pauli. The theorem statement will likely need to be adjusted too, with something
   like ~(In p ps).
 *)

Lemma interpret_HPaulis_herm :
  forall (decls : list string) (ps : list HPauli) (M : Square (2 ^ List.length decls)),
    interpret_HPaulis decls ps = Some M -> Herm M.
Proof.
  intros decls ps. generalize dependent decls.
  induction ps as [|p ps']; intros.
  - inversion H. apply herm_I.
  - inversion H.
    destruct (interpret_HPauli decls p) eqn:E1; try discriminate.
    destruct (interpret_HPaulis decls ps') eqn:E2; try discriminate.
    inversion H1. apply herm_mult.
    + eapply interpret_HPauli_WF. apply E1.
    + eapply interpret_HPaulis_WF. apply E2.
    + eapply interpret_HPauli_herm. apply E1.
    + eapply IHps'. apply E2.
    + eapply HPauli_terms_commute.
      * apply E1.
      * apply E2.
Qed.

Lemma interpret_TIH_Term_herm :
  forall (decls : list string) (s : TIH_Term) (M : Square (2 ^ List.length decls)),
    interpret_TIH_Term decls s = Some M -> Herm M.
Proof.
  intros. unfold interpret_TIH_Term in H.
  destruct (interpret_HPaulis decls (hPaulis s)) eqn:E; try discriminate.
  inversion H.
  apply interpret_HPaulis_herm in E.
  apply herm_scale. assumption.
Qed.

Lemma interpret_TIH_Terms_herm : 
  forall (decls : list string) (ss : list TIH_Term) (M : Square (2 ^ List.length decls)),
    interpret_TIH_Terms decls ss = Some M -> Herm M.
Proof.
  intros decls ss. generalize dependent decls. induction ss as [|t T].
  - intros. inversion H. apply herm_Zero.
  - intros. inversion H. destruct (interpret_TIH_Term decls t) eqn:E1.
    + destruct (interpret_TIH_Terms decls T) eqn:E2.
      * apply IHT in E2. inversion H1. apply herm_plus.
        -- eapply interpret_TIH_Term_herm. apply E1.
        -- assumption.
      * discriminate.
    + discriminate.
Qed.

(* Main lemma showing interpretation returns Hermitian matrices *)
Theorem term_herm {n : nat} : forall (P : H_Program) (T : HSF_Term) (S : Square n) H,
    sem_term P T S -> interpret_term P T = Some H -> Herm H.
Proof.
  intros P T S H Hsem Hit.
  unfold interpret_term in Hit. eapply interpret_TIH_Terms_herm.
  apply Hit.
Qed.

Corollary term_diagonalizable {n : nat} :
  forall (P : H_Program) (T : HSF_Term) (S : Square n) H,
    sem_term P T S -> interpret_term P T = Some H -> Diagonalizable H.
Proof.
  intros. apply herm_diagonalizable. eapply term_herm. apply H0. apply H1.
Qed.




(********************************)
(** Lemmas involving commuting **)
(********************************)

Lemma ham_commute_terms : forall (P : H_Program) (T1 T2 : HSF_Term),
    ham_commute P T1 T2 ->
    exists H1 H2, interpret_term P T1 = Some H1 /\ interpret_term P T2 = Some H2 /\
                  Mat_commute H1 H2.
Proof.
  intros.
  destruct (interpret_term P T1) eqn:E1.
  - destruct (interpret_term P T2) eqn:E2.
    + exists m, m0. unfold ham_commute in H.
      rewrite E1 in H. rewrite E2 in H. auto.
    + exfalso. unfold ham_commute in H.
      rewrite E1 in H. rewrite E2 in H. auto.
  - exfalso. unfold ham_commute in H.
    rewrite E1 in H. auto.
Qed.

(* If Hamiltonians commute, then so do their semantic matrices *)
Lemma ham_commute_term_semantics {n : nat} :
  forall (P : H_Program) (H1 H2 : HSF_Term) (S1 S2 : Square n),
  sem_term P H1 S1 -> sem_term P H2 S2 ->
  ham_commute P H1 H2 -> Mat_commute S1 S2.
Proof.
  intros P H1 H2 S1 S2 HH1 HH2 Hcomm.
  remember HH1 as HH1'. remember HH2 as HH2'. clear HeqHH1' HeqHH2'.
  destruct (ham_commute_terms P H1 H2 Hcomm) as [M1 [M2 [HM1 [HM2 HMcomm]]]]. clear Hcomm.
  unfold sem_term in HH1. rewrite HM1 in HH1. inversion HH1 as [Hd HS1]. clear HH1.
  unfold sem_term in HH2. rewrite HM2 in HH2. inversion HH2 as [Hd2 HS2]. clear HH2 Hd2.
  assert (Hherm : Diagonalizable (- Ci * sem_HScalar (Duration H1) * one_over_h_bar .* M1
                                  .+ - Ci * sem_HScalar (Duration H2) * one_over_h_bar .* M2)).
  {
    repeat (rewrite <- Mscale_assoc). rewrite <- Mscale_plus_distr_r.
    apply diag_scale. apply herm_diagonalizable. apply herm_plus; repeat (apply herm_scale).
    - eapply term_herm. apply HH1'. apply HM1.
    - eapply term_herm. apply HH2'. apply HM2.
  }
  remember (mat_exp_well_defined_diag (- Ci * sem_HScalar (Duration H1) * one_over_h_bar .* M1
      .+ - Ci * sem_HScalar (Duration H2) * one_over_h_bar .* M2) Hherm) as HM12_.
  inversion HM12_ as [S12 HM12]. clear HeqHM12_ HM12_.
  unfold Mat_commute. subst.
  assert (H : S1 × S2 = S12). {
    apply mat_exp_commute_add_diag with
        (M := (- Ci * sem_HScalar (Duration H1) * one_over_h_bar .* M1))
        (N := (- Ci * sem_HScalar (Duration H2) * one_over_h_bar .* M2)).
    - apply diag_scale. eapply term_diagonalizable.
      + apply HH1'.
      + apply HM1.
    - apply diag_scale. eapply term_diagonalizable.
      + apply HH2'.
      + apply HM2.      
    - apply HS1.
    - apply HS2.
    - apply HM12.
    - unfold Mat_commute.
      rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_r.
      rewrite Mscale_mult_dist_l. rewrite Mscale_mult_dist_l.
      rewrite Mscale_assoc. rewrite Mscale_assoc.
      rewrite HMcomm. rewrite Cmult_comm.
      reflexivity.
  }
  rewrite H. symmetry.
  apply mat_exp_commute_add_diag with
      (N := (- Ci * sem_HScalar (Duration H1) * one_over_h_bar .* M1))
      (M := (- Ci * sem_HScalar (Duration H2) * one_over_h_bar .* M2)).
  - apply diag_scale. eapply term_diagonalizable.
    + apply HH2'.
    + apply HM2.
  - apply diag_scale. eapply term_diagonalizable.
    + apply HH1'.
    + apply HM1.  
  - apply HS2.
  - apply HS1.
  - rewrite Mplus_comm. apply HM12.
  - unfold Mat_commute.
    rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l. rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc. rewrite Mscale_assoc.
    rewrite HMcomm. rewrite Cmult_comm.
    reflexivity.
Qed.




(*****************************************)
(** Lemmas about term/program semantics **)
(*****************************************)

(* Term semantics are well-formed *)
Lemma term_semantics_WF {n : nat} : forall (P : H_Program) (T : HSF_Term) (S : Square n),
    sem_term P T S -> WF_Matrix S.
Proof.
  intros P T S HT. remember HT as HT'. clear HeqHT'. unfold sem_term in HT.
  destruct (interpret_term P T) as [M |] eqn:E; try contradiction.
  inversion HT as [Hdims HS]. clear HT. subst.
  remember E as E'. clear HeqE'.
  apply interpret_term_WF in E.
  eapply mat_exp_WF_herm.
  - eapply term_herm.
    + apply HT'.
    + apply E'.
  - apply HS.
  - apply E.
Qed.

(* The effects of a Hamitonian are deterministic; i.e. semantics are unique *)
Lemma term_semantics_unique {n : nat} :
  forall (P : H_Program) (T : HSF_Term) (S1 S2 : Square n),
    sem_term P T S1 -> sem_term P T S2 -> S1 = S2.
Proof.
  intros P T S1 S2 HS1 HS2.
  remember HS1 as HS1'. clear HeqHS1'.
  unfold sem_term in HS1. unfold sem_term in HS2.
  destruct (interpret_term P T) as [M |] eqn:E; try contradiction.
  eapply mat_exp_unique_herm with (M0 := M).
  - eapply term_herm.
    + apply HS1'.
    + auto.
  - inversion HS1; subst. apply H0.
  - inversion HS2; subst. apply H0.
Qed.

(* The effects of a Hamitonian program are deterministic; i.e. semantics are unique *)
Lemma prog_semantics_unique {n : nat} : forall (P : H_Program) (S1 S2 : Square n),
    sem_program P S1 -> sem_program P S2 -> S1 = S2.
Proof.
  intros P S1 S2 HS1 HS2. generalize dependent S2. induction HS1; intros S2 HS2.
  - inversion HS2. reflexivity.
  - inversion HS2; subst. clear Hdims0.
    assert (HSP : SP = SP0). {
      apply IHHS1. assumption.
    }
    assert (HSt : St = St0). {
      eapply term_semantics_unique. apply Ht. assumption.
    }
    subst. reflexivity.
Qed.
  
(* The semantics of a term depend only on the declarations of the program 
   (not on the Hamiltonian terms) *)
Lemma sem_term_depends_on_D : forall P1 P2 H (S : Square (dims P1)),
    sem_term P1 H S -> Decls P1 = Decls P2 -> sem_term P2 H S.
Proof.
  intros P1 P2 H S Ht Hd. unfold sem_term in Ht.
  destruct (interpret_term P1 H) eqn:E.
  - inversion Ht. clear Ht.
    unfold sem_term.
    assert (Hdims : dims P1 = dims P2). {
      unfold dims. unfold count_sites. rewrite Hd. reflexivity.
    }
    assert (H2 : interpret_term P2 H = Some m). {
      subst. rewrite <- E. unfold interpret_term. rewrite Hd. rewrite Hdims. reflexivity.
    }
    rewrite H2. split.
    + symmetry. subst. assumption.
    + rewrite <- Hdims. assumption.
  - contradiction.
Qed.

(* The semantics of a 2-term program are the same as the product of the semantics of the
   individual terms *)
Lemma two_term_program_semantics :
  forall (P : H_Program) (H1 H2 : HSF_Term) (St1 St2 SP : Square (dims P)),
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program {| Decls := P.(Decls); Terms := [H2; H1] |} SP ->
    SP = St2 × St1.
Proof.
  intros P H1 H2 St1 St2 SP HSt1 HSt2 HP.
  assert (HP' : sem_program {| Decls := Decls P; Terms := [H1] |} (St1 × I (dims P))). {
    apply sem_program_cons.
    - eapply sem_term_depends_on_D.
      + apply HSt1.
      + reflexivity.
    - apply sem_program_nil. 
      + remember (semantics_implies_no_terms_valid {| Decls := Decls P; Terms := [H2; H1] |}
                                                   SP HP) as HH. clear HeqHH.
        simpl in HH. assumption.
      + remember (extract_dims {| Decls := Decls P; Terms := [H2; H1] |} SP HP) as Hdims.
        clear HeqHdims. unfold dims in *. unfold count_sites in *. simpl in *. assumption.
    - apply semantics_implies_program_valid in HP.
      eapply term_removal_valid with (t := H2) (T := [H1]) in HP.
      + simpl in HP. assumption.
      + reflexivity.
    - apply extract_dims in HP. unfold dims in *. unfold count_sites in *.
      simpl in *. assumption.
  }
  assert (HP'' : sem_program {| Decls := Decls P; Terms := [H2; H1] |}
                             (St2 × (St1 × I (dims P)))).
  {
    apply sem_program_cons.
    - eapply sem_term_depends_on_D.
      + apply HSt2.
      + reflexivity.
    - assumption.
    - apply semantics_implies_program_valid in HP. assumption.
    - apply extract_dims in HP'. unfold dims in *. unfold count_sites in *.
      simpl in *. assumption.
  }
  assert (HMmultI : St1 × I (dims P) = St1). {
    apply Mmult_1_r. apply term_semantics_WF in HSt1. assumption.
  }
  rewrite HMmultI in HP''. eapply prog_semantics_unique.
  apply HP. apply HP''.
Qed.




(******************)
(** Main Theorem **)
(******************)


(* Commuting Hamiltonians have the same semantics *)
Theorem commuting_Ham_semantics (H1 H2 : HSF_Term) :
  forall (P : H_Program) (D : list string) (St1 St2 SP1 SP2 : Square (dims P)),
    D = P.(Decls) ->
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program (makeHProg D [H2; H1]) SP1 -> sem_program (makeHProg D [H1; H2]) SP2 ->
    ham_commute P H1 H2 ->
    SP1 = SP2.
Proof.
  intros P D St1 St2 SP1 SP2 HD Ht1 Ht2 HP1 HP2 Hcomm.
  remember (ham_commute_term_semantics P H1 H2 St1 St2 Ht1 Ht2 Hcomm) as H.
  clear HeqH Hcomm. rename H into Hcomm.
  assert (H : SP1 = St2 × St1 -> SP2 = St1 × St2 -> SP1 = SP2).
  { intros HSP1 HSP2. subst. symmetry. apply Hcomm. }
  apply H.
  - subst. apply (two_term_program_semantics P H1 H2 St1 St2 SP1); assumption.
  - subst. apply (two_term_program_semantics P H2 H1 St2 St1 SP2); assumption.
Qed.
