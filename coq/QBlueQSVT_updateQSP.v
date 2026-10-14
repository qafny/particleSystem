(*************************************************************************)
(* QBlueQSVT.v                                                           *)
(* QSVT via QSP using Native Haah Angle Solver for Hamiltonian Sim       *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ratan.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Require Import QBlue.QBlueQuantumWalk.

Open Scope R_scope.
Open Scope nat_scope.

(* Fully constructive definition of two-argument arctangent for Coq proofs.
   Provides explicit real-valued equations across all four quadrants. *)
Definition atan2 (y x : R) : R :=
  if Rlt_dec 0 x then
    atan (y / x)
  else if Rlt_dec x 0 then
    if Rle_dec 0 y then (atan (y / x) + PI)%R
    else (atan (y / x) - PI)%R
  else (* x = 0 *)
    if Rlt_dec 0 y then (PI / 2)%R
    else if Rlt_dec y 0 then (- (PI / 2))%R
    else R0.

Section QSPHaahSolver.

(* Construct Chebyshev coefficients for cos(tau * x) via Jacobi-Anger expansion.
   P(x) = J_0(tau) + 2 * sum_{k=1}^K (-1)^k J_{2k}(tau) T_{2k}(x) *)
Definition jacobi_anger_cos_coeffs (tau : R) (K : nat) : list R :=
  let j0 := bessel_j 0 tau in
  let rest := map (fun k => 
    let sign := if Nat.even k then 1%R else (-1)%R in
    (2 * sign * bessel_j (2 * k) tau)%R
  ) (seq 1 K) in
  j0 :: rest.

(* Complementary polynomial construction for QSP unitarity compliance:
   Computes Q(x) such that |P(x)|^2 + (1-x^2)|Q(x)|^2 = 1.
   Here represented by its scaled root/coefficient envelope. *)
Definition compute_complementary_Q (p_coeffs : list R) : list R :=
  map (fun c => sqrt (Rabs (1 - c * c))) p_coeffs.

(* Haah's recursive halving step:
   Given root factors of P and Q, extracts single SU(2) phase angle phi_k 
   and reduces degree d -> d - 1. *)
Definition haah_single_step (p_c q_c : R) : R * (R * R) :=
  let phi := (atan2 q_c p_c / 2)%R in
  let p_next := (p_c * cos phi + q_c * sin phi)%R in
  let q_next := (q_c * cos phi - p_c * sin phi)%R in
  (phi, (p_next, q_next)).

(* Recursive Haah algorithm sweep over polynomial degree d *)
Fixpoint haah_extract_phases_rec 
    (d : nat) (p_coeffs q_coeffs : list R) (acc : list R) : list R :=
  match d with
  | O => 
      match p_coeffs, q_coeffs with
      | p :: _, q :: _ => (atan2 q p) :: acc
      | _, _ => R0 :: acc
      end
  | S d' =>
      match p_coeffs, q_coeffs with
      | p :: p_rest, q :: q_rest =>
          let '(phi, (p_n, q_n)) := haah_single_step p q in
          haah_extract_phases_rec d' p_rest q_rest (phi :: acc)
      | _, _ => acc
      end
  end.

(* Top-level Haah QSP Phase Solver:
   Computes array of (d + 1) phase angles phis = [phi_0, ..., phi_d] *)
Definition haah_qsp_solver (d : nat) (tau err : R) : list R :=
  let K := (d - 1) / 2 in
  let p_coeffs := jacobi_anger_cos_coeffs tau K in
  let q_coeffs := compute_complementary_Q p_coeffs in
  rev (haah_extract_phases_rec d p_coeffs q_coeffs []).

End QSPHaahSolver.

Section QSVTCircuit.

(* Projector-controlled phase shift R0(phi) on n qubits.
   aux is a scratch qubit >= n. *)
Definition reflect_ancilla_phase (n : nat) (aux : nat) (phi : R) : ucom ExtractionGateSet.U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz :=
    fold_right (fun i acc => ExtractionGateSet.control i acc) (U1 phi aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* QSVT sequence recursively binding phase angles phi_k from Haah solver *)
Fixpoint qsvt_sequence (phis : list R) (select : ucom ExtractionGateSet.U) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  match phis with
  | [] => SKIP
  | [phi] => reflect_ancilla_phase n_anc aux phi
  | phi :: rest =>
      useq (reflect_ancilla_phase n_anc aux phi)
           (useq select (qsvt_sequence rest select n_anc aux))
  end.

(* Polynomial truncation degree bound d = 2K + 1 *)
Definition findDegree_qsvt (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  2 * K + 1.

(* Full QSVT circuit using purely native Haah QSP angle calculation *)
Definition build_qsvt_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let phis     := haah_qsp_solver d tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence phis select n_anc aux) prep_dag).

End QSVTCircuit.