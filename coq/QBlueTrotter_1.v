
(***************************************************************
 * QBlueTrotter_1.v
 *
 * First-order and second-order Trotterization for
 * real-coefficient Pauli Hamiltonians.
 *
 * Mathematical foundations:
 *   QBlueHamiltonian.v
 *   QBlueMatNorm.v
 *   QBlueMatrixExp.v

 ***************************************************************)

From Coq Require Import Reals List Arith PeanoNat Bool.
From Coq Require Import Psatz Lia ZArith.

Require Import QuantumLib.Complex.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueHamiltonian.
Require Import QBlue.QBlueMatNorm.
Require Import QBlue.QBlueMatrixExp.

Import ListNotations.
Local Open Scope R_scope.

(* ============================================================ *)
(* 1. Local utilities                                           *)
(* ============================================================ *)

(* Natural-number ceiling for nonnegative reals. *)

Definition ceilR_N (x : R) : nat :=
  if Rle_dec x 0 then
    0%nat
  else
    let z := (up x - 1)%Z in
    if Req_EM_T x (IZR z)
    then Z.to_nat z
    else Z.to_nat (up x).

(* Scale every real Hamiltonian coefficient. *)

Definition mult_r_normprog
  (c : R) (ap : norm_prog) : norm_prog :=
  map (fun term => (c * fst term, snd term)) ap.

(* ============================================================ *)
(* 2. Pauli operators                                           *)
(* ============================================================ *)

Definition pauli_is_identity (p : paulimat) : bool :=
  match p with
  | paulii => true
  | _ => false
  end.

Definition pauli_equal (p q : paulimat) : bool :=
  match p, q with
  | paulix, paulix => true
  | pauliy, pauliy => true
  | pauliz, pauliz => true
  | paulii, paulii => true
  | _, _ => false
  end.

Definition pauli_terms
  (n : nat) (input : norm_prog)
  : list (R * list paulimat) :=
  map
    (fun term =>
       (Rabs (fst term),
        map (snd term) (seq 0 n)))
    input.

(* ============================================================ *)
(* 3. Pauli anticommutation                                     *)
(* ============================================================ *)

Fixpoint anti_count
  (a b : list paulimat) : nat :=
  match a, b with
  | x :: xs, y :: ys =>
      ((if andb
          (andb
            (negb (pauli_is_identity x))
            (negb (pauli_is_identity y)))
          (negb (pauli_equal x y))
        then 1%nat else 0%nat)
       + anti_count xs ys)%nat
  | _, _ => 0%nat
  end.

Definition pauli_anticommute
  (a b : list paulimat) : bool :=
  Nat.odd (anti_count a b).

(* ============================================================ *)
(* 4. Commutator weights                                        *)
(* ============================================================ *)

Fixpoint comm_weight
  (c : R)
  (p : list paulimat)
  (rest : list (R * list paulimat)) : R :=
  match rest with
  | [] => 0
  | (c', p') :: r =>
      (if pauli_anticommute p p'
       then 2 * c * c'
       else 0)
      + comm_weight c p r
  end.

Fixpoint weight_sum
  (l : list (R * list paulimat)) : R :=
  match l with
  | [] => 0
  | (c, _) :: r => c + weight_sum r
  end.

(* ============================================================ *)
(* 5. First-order commutator bound                              *)
(* ============================================================ *)

Fixpoint comm_sum1
  (l : list (R * list paulimat)) : R :=
  match l with
  | [] => 0
  | (c, p) :: rest =>
      comm_weight c p rest + comm_sum1 rest
  end.

(* ============================================================ *)
(* 6. Second-order commutator bound                             *)
(* ============================================================ *)

Fixpoint comm_sum2
  (l : list (R * list paulimat)) : R :=
  match l with
  | [] => 0
  | (c, p) :: rest =>
      comm_weight c p rest *
        (weight_sum rest / 6 + c / 12)
      + comm_sum2 rest
  end.

(* ============================================================ *)
(* 7. First-order step count                                    *)
(* ============================================================ *)

Definition trotter_step
  (err t : R)
  (n : nat)
  (input : norm_prog) : nat :=
  if Rlt_dec 0 err then
    let C1 := comm_sum1 (pauli_terms n input) in
    Nat.max 1%nat
      (ceilR_N (t * t * C1 / (2 * err)))
  else
    1%nat.

(* ============================================================ *)
(* 8. First-order Trotterization                                *)
(* ============================================================ *)

Definition trotter_astep
  (N : R)
  (ap : norm_prog) : norm_prog :=
  mult_r_normprog (1 / N) ap.

Fixpoint trotter_nstep_acc
  (N : nat)
  (ap : norm_prog)
  (acc : norm_prog) : norm_prog :=
  match N with
  | O => rev acc
  | S k =>
      trotter_nstep_acc k ap (rev_append ap acc)
  end.

Definition trotter_nstep
  (N : nat)
  (ap : norm_prog) : norm_prog :=
  trotter_nstep_acc N ap [].

Definition trotter
  (err t : R)
  (n : nat)
  (input : norm_prog) : norm_prog :=
  let N := trotter_step err t n input in
  let astep := trotter_astep (INR N) input in
  trotter_nstep N astep.

(* ============================================================ *)
(* 9. Second-order step count                                   *)
(* ============================================================ *)

Definition trotter_step_2nd_order
  (err t : R)
  (n : nat)
  (input : norm_prog) : nat :=
  if Rlt_dec 0 err then
    let C2 :=
      comm_sum2 (pauli_terms n (rev input)) in
    Nat.max 1%nat
      (ceilR_N
        (sqrt
          (Rabs t * Rabs t * Rabs t * C2 / err)))
  else
    1%nat.

(* ============================================================ *)
(* 10. Second-order symmetric Trotterization                    *)
(* ============================================================ *)

Definition trotter_2nd_order
  (err t : R)
  (n : nat)
  (input : norm_prog) : norm_prog :=
  let N := trotter_step_2nd_order err t n input in
  let astep1 :=
    trotter_astep (2 * INR N) (rev input) in
  let astep2 :=
    trotter_astep (2 * INR N) input in
  trotter_nstep N (astep1 ++ astep2).

(* ============================================================ *)
(* 11. Structural correctness                                   *)
(* ============================================================ *)

Lemma mult_r_normprog_length :
  forall c ap,
    length (mult_r_normprog c ap) = length ap.
Proof.
  intros c ap.
  unfold mult_r_normprog.
  apply map_length.
Qed.

Lemma pauli_terms_length :
  forall n input,
    length (pauli_terms n input) = length input.
Proof.
  intros n input.
  unfold pauli_terms.
  apply map_length.
Qed.

Lemma trotter_nstep_acc_length :
  forall N ap acc,
    length (trotter_nstep_acc N ap acc) =
    (N * length ap + length acc)%nat.
Proof.
  induction N as [| N IH]; intros ap acc.
  - simpl.
    rewrite rev_length.
    lia.
  - simpl.
    rewrite IH.
    rewrite rev_append_rev.
    rewrite app_length.
    rewrite rev_length.
    lia.
Qed.


Lemma trotter_nstep_length :
  forall N ap,
    length (trotter_nstep N ap) =
    (N * length ap)%nat.
Proof.
  intros N ap.
  unfold trotter_nstep.
  rewrite trotter_nstep_acc_length.
  simpl.
  lia.
Qed.

Lemma trotter_astep_length :
  forall N ap,
    length (trotter_astep N ap) = length ap.
Proof.
  intros N ap.
  unfold trotter_astep.
  apply mult_r_normprog_length.
Qed.

Lemma trotter_length :
  forall err t n input,
    length (trotter err t n input) =
    (trotter_step err t n input *
       length input)%nat.
Proof.
  intros err t n input.
  unfold trotter.
  rewrite trotter_nstep_length.
  rewrite trotter_astep_length.
  reflexivity.
Qed.

Lemma trotter_2nd_order_length :
  forall err t n input,
    length (trotter_2nd_order err t n input) =
    (2 * trotter_step_2nd_order err t n input *
       length input)%nat.
Proof.
  intros err t n input.
  unfold trotter_2nd_order.
  rewrite trotter_nstep_length.
  rewrite app_length.
  repeat rewrite trotter_astep_length.
  rewrite rev_length.
  lia.
Qed.

(* ============================================================ *)
(* 12. Positivity of step counts                                *)
(* ============================================================ *)

Lemma trotter_step_positive :
  forall err t n input,
    (1 <= trotter_step err t n input)%nat.
Proof.
  intros err t n input.
  unfold trotter_step.
  destruct (Rlt_dec 0 err); lia.
Qed.

Lemma trotter_step_2nd_order_positive :
  forall err t n input,
    (1 <= trotter_step_2nd_order err t n input)%nat.
Proof.
  intros err t n input.
  unfold trotter_step_2nd_order.
  destruct (Rlt_dec 0 err); lia.
Qed.


















































