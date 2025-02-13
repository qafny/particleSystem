(** -- Trotterize.v -- **)
(**
 * Compiler that takes H_Program to QasmProgram.
 * The main step uses the "Trotterization" algorithm.
 *)

Require Import String.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import Qasm.
Require Import Semantics.
Require Import PauliRotations.
Require Import MatrixExponential.

(* AST Transform of an one-local term *)
Definition makeQT1 (p : Pauli) (theta : HScalar) (loc : nat) :=
  match p with
  | Pauli_I => []
  | Pauli_X => [QasmTerm1 (Rx theta) loc]
  | Pauli_Y => [QasmTerm1 (Ry theta) loc]
  | Pauli_Z => [QasmTerm1 (Rz theta) loc]
  end.

(* Correctness of above *)
Lemma makeQT1_correct :
  forall (num_qubits : nat) (p : Pauli) (theta : HScalar) (loc : nat),
    (loc < num_qubits)%nat ->
    QasmInstsSemantics
        num_qubits
          (makeQT1 p theta loc)
          (padIs num_qubits (PauliToExpM p (sem_HScalar theta)) loc).
Proof.
  intros.
  induction p.
  - simpl.
    unfold RIGate.
    Search padIs.
    rewrite padIs_scale.
    exists (/ (Cexp (- sem_HScalar theta / 2))).
    rewrite Mscale_assoc.
    Locate "/".
    Search Cinv.
    rewrite Cinv_l.
    rewrite Mscale_1_l.
    unfold padIs.
    Search kron.
    rewrite id_kron.
    rewrite id_kron.
    assert (Simpl_LHS : (2 ^ loc * 2 * 2 ^ (num_qubits - loc - 1) = 2 ^ num_qubits)%nat).
    (* Arithmetics... *)
    admit.
    rewrite Simpl_LHS.
    reflexivity.
    apply Cexp_nonzero.
  - simpl.
    eexists.
    eexists.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    exists R1.
    rewrite Mscale_1_l.
    Search I.
    rewrite Mmult_1_r.
    reflexivity.
    Print reflect.
    Search padIs.
    apply padIs_WF.
    admit. (* RXGate WF... Need to prove *)
    assumption.
  - simpl.
    eexists.
    eexists.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    exists R1.
    rewrite Mscale_1_l.
    Search I.
    rewrite Mmult_1_r.
    reflexivity.
    Print reflect.
    Search padIs.
    apply padIs_WF.
    admit. (* RYGate WF... Need to prove *)
    assumption.
  - simpl.
    eexists.
    eexists.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    split.
    exists R1.
    rewrite Mscale_1_l.
    reflexivity.
    exists R1.
    rewrite Mscale_1_l.
    Search I.
    rewrite Mmult_1_r.
    reflexivity.
    Print reflect.
    Search padIs.
    apply padIs_WF.
    admit. (* RZGate WF... Need to prove *)
    assumption.
Admitted.

(* More constants *)
Definition HScPI := HScReal PI "pi".
Definition HScPI2 := HScReal (PI / 2) "(pi/2)".
Definition HScZero := HScReal 0 "0".

(* Hard-coded gates *)
Definition QasmTYZ := QasmU HScPI2 HScZero HScPI2.
Definition QasmTYZ_dag := QasmU HScPI2 HScPI2 HScPI.

(* AST transform of a 2-local term *)
Definition makeQT2 (p1 p2 : Pauli)
           (theta : HScalar)
           (loc1 loc2 : nat) : list QasmTerm :=
  match (p1, p2) with
  | (Pauli_I, _) => makeQT1 p2 theta loc2
  | (_, Pauli_I) => makeQT1 p1 theta loc1
  | (Pauli_X, Pauli_X) => [QasmTerm2 (Rxx theta) loc1 loc2]
  | (Pauli_X, Pauli_Y) => [QasmTerm1 QasmH loc1; QasmTerm1 QasmTYZ loc2;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmH loc1; QasmTerm1 QasmTYZ_dag loc2]
  | (Pauli_X, Pauli_Z) => [QasmTerm1 QasmH loc1;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmH loc1]
  | (Pauli_Y, Pauli_X) => [QasmTerm1 QasmTYZ loc1; QasmTerm1 QasmH loc2;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmTYZ_dag loc1; QasmTerm1 QasmH loc2]
  | (Pauli_Y, Pauli_Y) => [QasmTerm1 QasmTYZ loc1; QasmTerm1 QasmTYZ loc2;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmTYZ_dag loc1; QasmTerm1 QasmTYZ_dag loc2]
  | (Pauli_Y, Pauli_Z) => [QasmTerm1 QasmTYZ loc1;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmTYZ_dag loc1]
  | (Pauli_Z, Pauli_X) => [QasmTerm1 QasmH loc2;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmH loc2]
  | (Pauli_Z, Pauli_Y) => [QasmTerm1 QasmTYZ loc2;
                           QasmTerm2 (Rzz theta) loc1 loc2;
                           QasmTerm1 QasmTYZ_dag loc2]
  | (Pauli_Z, Pauli_Z) => [QasmTerm2 (Rzz theta) loc1 loc2]
  end.

(* TODO Correctness of above *)
(*
Lemma makeQT2_correct :
  forall theta loc1 loc2,
    loc1 =? loc2 = false ->
    matrix_exponential (makeQT2 p1 p2 theta loc1 loc2)
*)

(* Conversion from natural numbers to HScalar type *)
(* TODO should unify naming style/convention *)
Definition natToHSc (n : nat) := HScReal (INR n) (string_of_nat n).

(**
 * Takes a TIH_Term and a total duration t to constructs quantum circuit
 * that runs the Hamiltonian evolution for a short time-slice of duration (t / nSlices).
 *)
Definition sliceTerm (decls : list string)
           (duration : HScalar)
           (term : TIH_Term)
           (nSlices : nat) : option (list QasmTerm) :=
  let theta := HScDiv (HScMult (natToHSc 2) (HScMult duration term.(hScale))) (natToHSc (nSlices)) in
  match term.(hPaulis) with
  | [] => Some []
  | [HIdOp site p] =>
      match find_qubit decls site with
      | None => None
      | Some loc => Some (makeQT1 p theta loc)
      end
  | [HIdOp site1 p1; HIdOp site2 p2] =>
      match (find_qubit decls site1, find_qubit decls site2) with
      | (Some loc1, Some loc2) => if loc1 =? loc2 then None else Some (makeQT2 p1 p2 theta loc1 loc2)
      | _ => None
      end
  | _ => None (* Too nonlocal *)
  end.

(* Correctness of above *)
Lemma sliceTermCorrect :
  forall decls duration term nSlices,
    sliceTerm decls duration term nSlices = None \/
      exists q_insts,
        sliceTerm decls duration term nSlices = Some q_insts /\
        exists Hi,
          (interpret_TIH_Term decls term = Some Hi) /\
          exists sem, (
           matrix_exponential (scale (- Ci * (sem_HScalar duration) / INR nSlices) Hi) sem /\
           QasmInstsSemantics (length decls) q_insts sem).
Proof.
  intros.
  destruct term.
  destruct hPaulis as [| p1].
  - (* Empty term; impossible AST? *)
    right.
    exists [].
    split.
    auto.
    exists (scale (sem_HScalar hScale) (I (2 ^ length decls))).
    split.
    + auto.
    + exists (scale (Cexp (- (sem_HScalar hScale) * (sem_HScalar duration) / INR nSlices))
                    (I (2 ^ length decls))).
      split.
      ++ rewrite Mscale_assoc.
         (* linear algebra incoming *)
         (* somehow apply mexp_scale? *)
         admit.
      ++ simpl.
         exists (/ Cexp (- sem_HScalar hScale * sem_HScalar duration / INR nSlices)).
         rewrite Mscale_assoc.
         rewrite Cinv_l.
         apply Mscale_1_l.
         apply Cexp_nonzero.
  - destruct hPaulis as [| p2].
    + (* 1-local *)
      destruct p1.
      case_eq (find_qubit decls loc).
      ++ (* qubit found *)
        intros.
        unfold sliceTerm.
        simpl.
        rewrite H.
        right.
        eexists. (* q_insts *)
        split.
        reflexivity.
        (* interpret TIH term *)
        unfold interpret_TIH_Term.
        unfold hPaulis.
        unfold interpret_HPaulis.
        rewrite <- interpret_HPauli'_correct.
        simpl.
        rewrite H.
        rewrite Mmult_1_r.
        eexists. (* TIH term exists *)
        split.
        reflexivity.
        exists (padIs
                  (length decls)
                  (PauliToExpM p (2 * sem_HScalar duration / INR nSlices * sem_HScalar hScale))
                  n).
        split.
        * (* Semantics is correct for hprog *)
          rewrite Mscale_assoc.
          rewrite <- padIs_scale.
          apply mexp_padIs.

           assert (lhs_simpl :
                    - Ci * sem_HScalar duration / INR nSlices * sem_HScalar hScale =
                      - Ci * (sem_HScalar duration / INR nSlices * sem_HScalar hScale)%R).
           admit. (* Arithmetic *)
           rewrite lhs_simpl.
           assert (rhs_simpl
                    : (2 * sem_HScalar duration / INR nSlices * sem_HScalar hScale)%R =
                        (2 * (sem_HScalar duration / INR nSlices * sem_HScalar hScale))%R ).
           admit. (* Arithmetic *)
           rewrite rhs_simpl.
           apply PauliToExpM_correct2t.
        * (* Qasm semantic matches *)
          Print makeQT1_correct.
          assert (HScalar_simpl :
                   sem_HScalar (HScDiv
                                  (HScMult (natToHSc 2) (HScMult duration hScale))
                                  (natToHSc nSlices))
                   = (2 * sem_HScalar duration / INR nSlices * sem_HScalar hScale)%R).
          (* HScalar computation... *)
          (* Don't want to deal with this right now. *)
          admit.
          rewrite <- HScalar_simpl.
          apply makeQT1_correct.
          admit. (* TODO find_qubit result should be in range *)
        * apply padIs_WF.
          Search PauliToMatrix.
          apply PauliToMatrix_WF.
          admit. (* again find_qubit output range *)
        ++ (* error case: site not found in decl *)
           intros.
           left.
           unfold sliceTerm.
           simpl.
           rewrite H.
           reflexivity.
    + destruct hPaulis as [| p3].
      * (* 2-local *)
        (* TODO this is going to be bad... *)
        destruct p1 as [site1 pauli1].
        destruct p2 as [site2 pauli2].
        case_eq (find_qubit decls site1).
        ** (* loc1 found *)
          intro loc1.
          intros.
          case_eq (find_qubit decls site2).
          *** (* loc2 found *)
            intro loc2.
            intros.
            case_eq (loc1 =? loc2).
            **** (* error: not really 2-local *)
              intros.
              left.
              unfold sliceTerm.
              simpl.
              rewrite H.
              rewrite H0.
              rewrite H1.
              reflexivity.
            **** (* TODO this will be bad *)
              intros.
              right.
              eexists.
              split.
              ***** (* q_insts *)
                unfold sliceTerm.
              simpl.
              rewrite H.
              rewrite H0.
              rewrite H1.
              simpl.
              reflexivity.
              ***** (* Hi *)
                
                
              admit.
          *** (* error: site2 not found *)
            left.
            unfold sliceTerm.
            simpl.
            rewrite H.
            rewrite H0.
            reflexivity.
        ** (* error: loc1 not found *)
          intros.
          left.
          unfold sliceTerm.
          simpl.
          rewrite H.
          reflexivity.
      * (* Too non-local *)
        left.
        unfold sliceTerm.
        simpl.
        destruct p1.
        destruct p2.
        reflexivity.
Admitted.

(* Given a list of TIH_terms, run each of them for a short time-slice. *)
Fixpoint sliceTerms (decls : list string)
         (duration : HScalar)
         (terms : list TIH_Term)
         (nSlices : nat) :=
  match terms with
  | head :: tail =>
      match (sliceTerm decls duration head nSlices, sliceTerms decls duration tail nSlices) with
      | (Some head_insts, Some tail_insts) => Some (head_insts ++ tail_insts)
      | _ => None
      end
  | [] => Some []
  end.

Definition sliceInst (decls : list string) (inst : HSF_Term) (nSlices : nat) :=
  sliceTerms decls inst.(Duration) inst.(Hamiltonian) nSlices.

Fixpoint accSlices (slice : list QasmTerm) (nSlices : nat) :=
  match nSlices with
  | O => []
  | S pr => slice ++ (accSlices slice pr)
  end.

(* The Trotterization algorithm for simulating Hamiltonian evolutions *)
Definition trotterizeInst (decls : list string) (inst : HSF_Term) (nSlices : nat) :=
  match sliceInst decls inst nSlices with
  | Some slice => Some (accSlices slice nSlices)
  | None => None
  end.

(* TODO State and prove correctness of above *)
(* Base on the approximation formula of matrix exponentials *)
(* Print matexp_approx. *)

(* Compilation of multiple instructions *)
Fixpoint trotterizeInsts (decls : list string) (insts : list HSF_Term) (nSlices : nat) :=
  match insts with
  | head :: tail =>
      match (trotterizeInst decls head nSlices, trotterizeInsts decls tail nSlices) with
      | (Some qasm_head, Some qasm_tail) => Some (qasm_head ++ qasm_tail)
      | _ => None
      end
  | [] => Some []
  end.

(**
 * Compilation results.
 * Maybe should just be an inductive type as follows:
 * `successful (output : QasmProgram) | failure`
 * or even just (optional QasmProgram) is fine... *)
Record trotterize_result := makeTrotRes
{
  successful : bool;
  output : QasmProgram;
}.

(* unnecessary *)
Definition idProg := makeQasmProg 0 [].

(* Overall compilation of H_Program *)
Definition trotterize (prog : H_Program) (nSlices : nat) :=
  match trotterizeInsts prog.(Decls) prog.(Terms) nSlices with
  | Some qasm_insts => makeTrotRes true (makeQasmProg (count_sites prog) qasm_insts)
  | None => makeTrotRes false idProg
  end.

(* Correctness of compilation *)
(* Part of the proof should probably be moved back as part of correctness of trotterizeInst *)
Theorem trotterize_correct :
  forall (hprog : H_Program) (correct_sem : Square (dims hprog)),
    (sem_program hprog correct_sem) ->
      ((forall nSlices, (trotterize hprog nSlices).(successful) = false) (* Cannot Trotterize *) \/
      ((forall nSlices, (trotterize hprog nSlices).(successful) = true) (* Can Trotterize *) /\
        exists (qasm_sem : nat -> (Square (dims hprog))),
          (forall nSlices, QasmSemantics (trotterize hprog nSlices).(output) (qasm_sem nSlices)) /\
          seq_conv (MatrixMetricSpace (dims hprog)) qasm_sem correct_sem
      )).
Proof.
  intro hprog.
  destruct hprog.
  generalize dependent Decls.
  induction Terms.
  - intros.
    right.
    intros.
    split.
    + auto.
    + exists (fun (_ : nat) => I (2 ^ (length Decls))).
      split.
      * intros.
        unfold QasmSemantics.
        simpl.
        exists 1.
        apply Mscale_1_l.
      * intro eps.
        intros.
        exists 1%nat.
        intros.
        simpl.
        assert (distzero : @dist_mats (dims (makeHProg Decls []))
                                      (I (2 ^ (length Decls)))
                                      (I (2 ^ (length Decls))) = 0).
        apply dist_mats_refl.
        reflexivity.
        (* TODO Prove that correct_sem = I and rewrite *)
        (*
        rewrite distzero.
        auto.
         *)
        admit.
  - intro decls.
    intro hprog_sem.
    intro hprog_sem_correct.
    inversion hprog_sem_correct; subst.
    clear Hdims.
    specialize (IHTerms decls).
    apply IHTerms in HP.
    destruct HP.
    + (* Cannot Trotterize *)
      left.
      intro nSlices.
      specialize (H nSlices).
      unfold trotterize.
      simpl.
      unfold trotterize in H.
      simpl in H.
      (* TODO *)
      admit.
    + destruct H as [CanTrotterizeTail QasmSemTail].
      right.
      split.
      * (* Can trotterize *)
        intro nSlices.
        specialize (CanTrotterizeTail nSlices).
        admit.
      * (* Exists semantics *)
        admit.
Admitted.


