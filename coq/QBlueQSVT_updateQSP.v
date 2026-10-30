(*************************************************************************)
(* QBlueQSVT_updateQSP.v                                                 *)
(* Two QSP phase solvers for Hamiltonian simulation via QSVT             *)
(*   1. haah_qsp_solver    — Haah 2019 (product decomposition + FFT)    *)
(*   2. donglin_qsp_solver — Dong, Meng, Whaley, Lin 2021 (BFGS opt.)  *)
(* Both are opaque Parameters extracted to OCaml via Extract Constant.  *)
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


(* ------------------------------------------------------------------ *)
(*  Solver 1: Haah 2019                                                *)
(*  "Product Decomposition of Periodic Functions in QSP"              *)
(*  Quantum 3:190, 2019. https://doi.org/10.22331/q-2019-10-07-190    *)
(*                                                                     *)
(*  Algorithm (Julia notebook, 6 steps):                              *)
(*   1. Jacobi-Anger even Laurent coefficients for cos(tau*x)/2       *)
(*   2. Evaluate A and C = sqrt(1-A^2) at D FFT roots of unity        *)
(*   3. Build 2x2 matrix polynomial F from A and C components         *)
(*   4. FFT F components to get coefficient matrices C[:,:,k]         *)
(*   5. Matrix iteration: extract d+1 phases from C                   *)
(*  Requires BigFloat for large tau; float64 for moderate tau.        *)
(* ------------------------------------------------------------------ *)
Parameter haah_qsp_solver : nat -> R -> R -> list R.


(* ------------------------------------------------------------------ *)
(*  Solver 2: Dong, Meng, Whaley, Lin 2021                            *)
(*  "Efficient Phase-Factor Evaluation in Quantum Signal Processing"  *)
(*  Phys. Rev. A 103, 042419.                                         *)
(*  https://doi.org/10.1103/PhysRevA.103.042419                       *)
(*                                                                     *)
(*  Algorithm (QSPBFGS):                                              *)
(*   1. Target f(x) = cos(tau*x)/2 at Chebyshev nodes x_k            *)
(*   2. Evaluate QSP polynomial P(Φ, x_k) via matrix product         *)
(*   3. Gradient ∂L/∂Φ analytically via forward-backward pass        *)
(*   4. L-BFGS quasi-Newton update of phase vector Φ                 *)
(*  Works in standard float64. Stable for any tau.                   *)
(* ------------------------------------------------------------------ *)
Parameter donglin_qsp_solver : nat -> R -> R -> list R.


Section QSVTCircuit.

(* Projector-controlled phase shift on n ancilla qubits; aux is scratch.
   Implements e^{i*phi*(I - |0...0><0...0|)} on the ancilla register. *)
Definition reflect_ancilla_phase (n aux : nat) (phi : R)
    : ucom ExtractionGateSet.U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz :=
    fold_right (fun i acc => ExtractionGateSet.control i acc) (U1 phi aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* QSVT sequence: phi_0 . SELECT . phi_1 . SELECT . ... . SELECT . phi_d
   For d+1 phases and d SELECT applications, implements a degree-d
   polynomial in the block-encoding of H/lambda. *)
Fixpoint qsvt_sequence (phis : list R) (select : ucom ExtractionGateSet.U)
    (n_anc aux : nat) : ucom ExtractionGateSet.U :=
  match phis with
  | []        => SKIP
  | [phi]     => reflect_ancilla_phase n_anc aux phi
  | phi :: rest =>
      useq (reflect_ancilla_phase n_anc aux phi)
           (useq select (qsvt_sequence rest select n_anc aux))
  end.

(* Polynomial truncation degree: d = 2K+1 where K is Bessel order.
   Returns the number of SELECT applications; haah/donglin return d+1 phases. *)
Definition findDegree_qsvt (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  2 * K + 1.


(* QSVT circuit using Haah 2019 phase solver.
   Use for moderate tau (lambda*t). May lose accuracy for large tau
   if the OCaml implementation uses float64 instead of BigFloat. *)
Definition build_qsvt_circuit_haah
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let phis     := haah_qsp_solver d tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence phis select n_anc aux) prep_dag).

(* QSVT circuit using Dong-Lin 2021 phase solver.
   Numerically stable for any tau in float64.
   Use for large tau or when high accuracy is required. *)
Definition build_qsvt_circuit_donglin
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let phis     := donglin_qsp_solver d tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence phis select n_anc aux) prep_dag).

(* Default: use Dong-Lin 2021 (more numerically stable in float64). *)
Definition build_qsvt_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  build_qsvt_circuit_donglin inner_prep select tau err n_anc aux.

End QSVTCircuit.