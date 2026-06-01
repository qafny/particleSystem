(* QBlueQubitization_opt.v — qubitization via QSP for Hamiltonian simulation.
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


(* ------------------------------------------------------------------ *)
(* ADDED: optimisations from Babbush et al. PRX 8, 041015 (2018).     *)
(* Requires QBlue.QBlueQROM and QBlue.QBluePEA to be compiled first. *)
(* ------------------------------------------------------------------ *)
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.
Require Import QBlue.QBlueQuantumWalk_opt.
Require Import QBlue.QBlueSyntax.

(* ADDED: optimised qubitization circuit.
   Replaces build_qubitization_circuit using:
     PREPARE = build_inner_prep_qrom (O(L) T, Babbush et al. Sec. III C/D)
     SELECT  = build_inner_select_unary (O(L) T, Babbush et al. Sec. III A)
   QSP sequence and walk_operator structure are unchanged.
   coeffs    : list of |alpha_j| Hamiltonian coefficients
   lp        : Hamiltonian lowprog (L Pauli terms)
   tau       : rescaled time parameter
   err       : target approximation error
   n_anc     : LCU ancilla register size = ceil(log2 L)
   aux       : scratch qubit for reflect_ancilla
   amp_m     : amplitude precision in bits for QROM
   qrom_out  : first QROM output qubit
   qrom_root : QROM root indicator ancilla
   qrom_pancs: n_anc QROM path ancilla qubits
   sel_root  : SELECT tree root ancilla
   sel_pancs : n_anc SELECT tree path ancilla qubits *)
Definition build_qubitization_circuit_opt
    (coeffs : list R) (lp : lowprog)
    (tau err : R) (n_anc aux amp_m qrom_out qrom_root sel_root : nat)
    (qrom_pancs sel_pancs : list nat)
    : ucom ExtractionGateSet.U :=
  let lam  := fold_left Rplus coeffs 0%R in
  let PREP := build_inner_prep_qrom coeffs lam n_anc amp_m
                qrom_out qrom_root qrom_pancs in
  let SEL  := build_inner_select_unary lp n_anc (length lp)
                sel_root sel_pancs in
  build_qubitization_circuit PREP SEL tau err n_anc aux.

(* ADDED: Heisenberg-limited PEA for qubitization (Babbush et al. Sec. II B).
   Replaces qsp_sequence with heis_pea, achieving Heisenberg-limit query
   complexity O(lambda/epsilon) vs O((lambda/epsilon) log(1/epsilon)) for QSP.
   Uses QROM PREPARE and unary iteration SELECT.
   The walk operator W is built from the optimised PREP and SELECT.
   m         : number of PEA control qubits; 2^m total W applications
   pea_base  : first PEA control qubit
   pea_anc   : ancilla qubit for prepare_chi
   All other parameters identical to build_qubitization_circuit_opt. *)
Definition build_qubitization_heis_pea
    (coeffs : list R) (lp : lowprog)
    (n_anc aux m pea_base pea_anc amp_m qrom_out qrom_root sel_root : nat)
    (qrom_pancs sel_pancs : list nat)
    : ucom ExtractionGateSet.U :=
  let lam  := fold_left Rplus coeffs 0%R in
  let PREP := build_inner_prep_qrom coeffs lam n_anc amp_m
                qrom_out qrom_root qrom_pancs in
  let SEL  := build_inner_select_unary lp n_anc (length lp)
                sel_root sel_pancs in
  heis_pea_from_lcu m pea_base pea_anc n_anc aux PREP SEL.