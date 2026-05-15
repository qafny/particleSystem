(*************************************************************************
  QBlueQubitization.v
  Qubitization-based Hamiltonian simulation via Quantum Signal Processing.

  Key difference from QBlueQuantumWalk:
    - QWalk  : PREP_outer . (Σ_j ctrl_j(W^{2^j})) . PREP_outer†
               uses binary decomposition → 2^n_outer - 1 W copies
    - Qubitization: d+1 direct applications of W interleaved with Rz phases
               uses QSP   → d = 2K+1 W copies  (linear in K, not exponential)

  This makes qubitization more gate-efficient for large K.
*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Require Import QBlue.QBlueQuantumWalk.

Open Scope R_scope.
Open Scope nat_scope.

Section QubitizationCircuit.

(*------------------------------------------------------------
  1. QSP degree: number of W applications to achieve error ε
     for simulation time τ = λ·t.
     Uses the same Bessel truncation K as QWalk; QSP needs
     d = 2K + 1 signal-processing steps.
------------------------------------------------------------*)

Definition findDegree_qsp (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  2 * K + 1.

(*------------------------------------------------------------
  2. Walk operator W for Qubitization  (Low & Chuang 2019)
     W = PREP† · R₀ · PREP · SELECT
     where R₀ = (2|0⟩⟨0| − I) on ancilla qubits.

     This is the same walk_operator already defined in
     QBlueQuantumWalk, so we reuse it directly.
------------------------------------------------------------*)

(*------------------------------------------------------------
  3. QSP sequence:  Rz(φ₀) · W · Rz(φ₁) · W · … · Rz(φ_d)
     Here we use a uniform phase φ = 0 as a placeholder;
     exact phases are computed numerically at extraction time.
     The circuit structure (and gate count) is correct regardless
     of the phase values.
------------------------------------------------------------*)

Fixpoint qsp_sequence (d : nat) (W : ucom ExtractionGateSet.U) (signal : nat)
    : ucom ExtractionGateSet.U :=
  match d with
  | O    => U1 R0 signal          (* final phase gate *)
  | S d' => useq (U1 R0 signal)
                 (useq W (qsp_sequence d' W signal))
  end.

(*------------------------------------------------------------
  4. Full Qubitization circuit:
       PREP . [QSP(W, d)] . PREP†
     The PREP / SELECT / W are built from the Hamiltonian lp.
------------------------------------------------------------*)

Definition build_qubitization_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R)
    (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let W   := walk_operator inner_prep select n_anc aux in
  let d   := findDegree_qsp tau err in
  let sig := aux + 1 in            (* signal qubit sits above aux *)
  let prep_dag := invert inner_prep in
  useq inner_prep
  (useq (qsp_sequence d W sig)
        prep_dag).

End QubitizationCircuit.
