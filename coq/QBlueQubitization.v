(* QBlueQubitization.v — qubitization via QSP for Hamiltonian simulation.
   Reuses walk_operator from QBlueQuantumWalk. *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Require Import QBlue.QBlueQuantumWalk.

Open Scope R_scope.
Open Scope nat_scope.

Section QubitizationCircuit.

(* QSP needs d = 2K+1 steps to achieve error err at time tau. *)
Definition findDegree_qsp (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  2 * K + 1.

(* Rz(0) · W · Rz(0) · W · ... d times.
   Phase values are placeholders; exact angles computed at extraction. *)
Fixpoint qsp_sequence (d : nat) (W : ucom ExtractionGateSet.U) (signal : nat)
    : ucom ExtractionGateSet.U :=
  match d with
  | O    => U1 R0 signal
  | S d' => useq (U1 R0 signal) (useq W (qsp_sequence d' W signal))
  end.

(* Full circuit: PREP . QSP(W, d) . PREP† *)
Definition build_qubitization_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let W       := walk_operator inner_prep select n_anc aux in
  let d       := findDegree_qsp tau err in
  let sig     := aux + 1 in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsp_sequence d W sig) prep_dag).

End QubitizationCircuit.
