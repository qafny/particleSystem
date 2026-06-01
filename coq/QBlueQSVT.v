(* QBlueQSVT.v — QSVT via QSP for Hamiltonian simulation.
   Reuses components from QBlueQuantumWalk. *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Require Import QBlue.QBlueQuantumWalk.

Open Scope R_scope.
Open Scope nat_scope.

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

(* QSVT sequence alternates select and reflect_ancilla_phase.
   Phases are placeholders of R0; exact values computed at extraction.
   For a degree d polynomial, we apply select d times and phase shifts d+1 times. *)
Fixpoint qsvt_sequence (d : nat) (select : ucom ExtractionGateSet.U) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  match d with
  | O    => reflect_ancilla_phase n_anc aux R0
  | S d' => useq (reflect_ancilla_phase n_anc aux R0)
                 (useq select (qsvt_sequence d' select n_anc aux))
  end.

Definition findDegree_qsvt (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  2 * K + 1.

(* Full circuit: PREP . QSVT(select, d) . PREP† *)
Definition build_qsvt_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence d select n_anc aux) prep_dag).

End QSVTCircuit.
