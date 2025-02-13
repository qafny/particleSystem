(** -- PauliRotations.v -- **)
(**
 * Defines some basic quantum operators as well as their matrix exponentials.
 *)

Require Import Complex.
Require Import QWIRE.Matrix.
Require Import MatrixExponential.
Require Import Diagonalization.

(* The Pauli group as defined in quantum information *)
Inductive Pauli :=
| Pauli_I
| Pauli_X
| Pauli_Y
| Pauli_Z.

Definition XGate : Square 2 := fun (i j : nat) =>
    match (i, j) with
    | (0, 1) => RtoC 1
    | (1, 0) => RtoC 1
    | _ => RtoC 0
    end.
    
Definition YGate : Square 2 := fun (i j : nat) =>
    match (i, j) with
    | (0, 1) => -Ci
    | (1, 0) => Ci
    | _ => RtoC 0
    end.

Definition ZGate : Square 2 := fun (i j : nat) =>
    match (i, j) with
    | (0, 0) => RtoC 1
    | (1, 1) => RtoC (-1)
    | _ => RtoC 0
    end.

(* The 1-qubit Hadamate gate *)
Definition HGate : Square 2 := fun (i j : nat) =>
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => / sqrt 2
  | (1, 0) => / sqrt 2
  | (1, 1) => - / sqrt 2
  | _ => 0
  end.

(* Diagonalization of the Pauli X matrix *)
Lemma XGateDiagonalization :
  Diagonalization XGate HGate ZGate HGate.
Proof.
  Admitted.

(* Maps the Pauli gates to their respective semantics *)
Definition PauliToMatrix (p : Pauli) : Square 2 :=
    match p with
    | Pauli_I => I 2
    | Pauli_X => XGate
    | Pauli_Y => YGate
    | Pauli_Z => ZGate
    end.

(* -- Matrix exponentials of scalar multiples of Pauli gates -- *)
(* Implemented by Qiskit *)
(* Maybe we should write the matrices out anyways? *)
Parameter RXGate : R -> Square 2.
Parameter RYGate : R -> Square 2.
Parameter RZGate : R -> Square 2.
Parameter RXXGate : R -> Square 4.
Parameter RZZGate : R -> Square 4.

Axiom RXGate_correct :
    forall (theta : R),
        matrix_exponential (scale (-Ci * theta / 2) XGate) (RXGate theta).

Axiom RYGate_correct :
    forall (theta : R),
        matrix_exponential (scale (-Ci * theta / 2) YGate) (RYGate theta).

Axiom RZGate_correct :
    forall (theta : R),
      matrix_exponential (scale (-Ci * theta / 2) ZGate) (RZGate theta).

(**
 * Physically speaking, RI = I.
 * Our definitions is however a bit shaky:
 * we have "global phase" issues so we have to write the following workaround.
 *)
Definition RIGate (theta : R) := scale (Cexp (-theta / 2)) (I 2).

Lemma RIGate_correct :
  forall (theta : R),
    matrix_exponential (scale (-Ci * theta / 2) (I 2)) (RIGate theta).
Proof.
Admitted.

(* Takes a single-qubit Pauli operator to its exponential *)
Definition PauliToExpM (p : Pauli) (theta : R) :=
  match p with
  | Pauli_I => RIGate theta
  | Pauli_X => RXGate theta
  | Pauli_Y => RYGate theta
  | Pauli_Z => RZGate theta
  end.

(* Correctness of the above *)
Lemma PauliToExpM_correct :
  forall (p : Pauli) (theta : R),
    matrix_exponential (scale (-Ci * theta / 2) (PauliToMatrix p)) (PauliToExpM p theta).
Proof.
  intros.
  induction p.
  apply RIGate_correct.
  apply RXGate_correct.
  apply RYGate_correct.
  apply RZGate_correct.
Qed.

(* The above lemma re-parametrized *)
Corollary PauliToExpM_correct2t :
  forall (p : Pauli) (theta2 : R),
    matrix_exponential (scale (-Ci * theta2) (PauliToMatrix p)) (PauliToExpM p (2 * theta2)).
Proof.
  (* Arithmetics...... *)
Admitted.

Definition RXYGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RXZGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RYYGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RYZGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

(* TODO correctness lemma..... *)

(* Three qubits rotation is nice to have but not top priority *)

(* -- Other useful quantum gates -- *)

(* Universal 1-qubit gate; provided by Qasm *)
Definition UGate (theta phi lambda : R) (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => cos(theta / 2)
  | (0, 1) => - Cexp lambda * sin(theta / 2)
  | (1, 0) => Cexp phi * sin(theta / 2)
  | (1, 1) => Cexp (phi + lambda) * cos(theta / 2)
  | _ => 0
  end.

(* Diagonalizing transform of the Pauli Y gate *)
Definition TYZ_Gate_dag (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => / sqrt 2
  | (1, 0) => Ci / sqrt 2
  | (1, 1) => -Ci / sqrt 2              
  | _ => 0
  end.

Lemma TYZ_Gate_dag_impl :
  TYZ_Gate_dag = UGate (PI / 2) (PI / 2) PI.
Proof.
Admitted.

(* The other half of the diagonalizing transform of Pauli Y gate *)
Definition TYZ_Gate (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => -Ci / sqrt 2
  | (1, 0) => / sqrt 2          
  | (1, 1) => Ci / sqrt 2              
  | _ => 0
  end.

Lemma TYZ_Gate_impl :
  TYZ_Gate = UGate (PI / 2) 0 (PI / 2).
Proof.
Admitted.

Lemma TYZ_correct :
  Diagonalization YGate TYZ_Gate_dag ZGate TYZ_Gate.
Proof.
Admitted.

(* -- Properties of Pauli operators -- *)

(* Pauli matrices are well-formed *)
Lemma PauliToMatrix_WF : forall (p : Pauli), WF_Matrix (PauliToMatrix p).
Proof.
  intros p. destruct p; simpl.
  - apply WF_I.
  - unfold WF_Matrix. intros.
    unfold XGate. destruct x.
    + destruct H.
      * lia.
      * destruct y; auto. destruct y; auto. lia.
    + destruct x; auto. destruct H.
      * lia.
      * destruct y; auto. lia.
  - unfold WF_Matrix. intros.
    unfold YGate. destruct x.
    + destruct H.
      * lia.
      * destruct y; auto. destruct y; auto. lia.
    + destruct x; auto. destruct H.
      * lia.
      * destruct y; auto. lia.
  - unfold WF_Matrix. intros.
    unfold ZGate. destruct x.
    + destruct H.
      * lia.
      * destruct y; auto. lia.
    + destruct x; auto. destruct H.
      * lia.
      * destruct y; auto. destruct y; auto. lia.
Qed.

(* Pauli matrices are Hermitian *)
Lemma PauliToMatrix_herm : forall (p : Pauli), Herm (PauliToMatrix p).
Proof.
  intros. destruct p; simpl.
  - apply herm_I.
  - intros i j. unfold Cconj.
    destruct i.
    + destruct j.
      * simpl. rewrite Ropp_0. auto.
      * destruct j; simpl; rewrite Ropp_0; auto.
    + destruct i; simpl.
      * destruct j; simpl.
        -- rewrite Ropp_0. auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
      * destruct j; simpl.
        -- rewrite Ropp_0; auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
  - intros i j. unfold Cconj.
    destruct i.
    + destruct j.
      * simpl. rewrite Ropp_0. auto.
      * destruct j; simpl.
        -- rewrite <- Ropp_0; auto.
        -- rewrite Ropp_0; auto.
    + destruct i; simpl.
      * destruct j; simpl.
        -- rewrite Ropp_0. rewrite Ropp_involutive. auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
      * destruct j; simpl.
        -- rewrite Ropp_0; auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
  - intros i j. unfold Cconj.
    destruct i.
    + destruct j.
      * simpl. rewrite Ropp_0. auto.
      * destruct j;
         simpl; rewrite Ropp_0; auto.
    + destruct i; simpl.
      * destruct j; simpl.
        -- rewrite Ropp_0. auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
      * destruct j; simpl.
        -- rewrite Ropp_0; auto.
        -- destruct j; simpl; rewrite Ropp_0; auto.
Qed.
