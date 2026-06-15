(* QBlueQubitization_opt.v — Qubitization via QSP with PRX optimisations only *)
(* Babbush et al. PRX 8, 041015 (2018), Sections II B, III A, III C/D *)
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.
Require Import QBlue.QBlueQuantumWalk_opt.


(* QSP degree d = 2K+1 to achieve error err at time tau *)
Definition findDegree_qsp (tau err : R) : nat :=
  2 * findK_qwalk tau err + 1.

(* QSP sequence: alternates U1 phase gates and walk operator W.
   Phase values are placeholders (R0); exact angles computed at extraction. *)
Fixpoint qsp_sequence (d : nat) (W : ucom ExtractionGateSet.U) (signal : nat)
    : ucom ExtractionGateSet.U :=
  match d with
  | O    => U1 R0 signal
  | S d' => useq (U1 R0 signal) (useq W (qsp_sequence d' W signal))
  end.


(* Optimised qubitization circuit (Babbush et al. PRX 2018):
     PREPARE = build_inner_prep_qrom  O(L) T gates  (Sec. III C/D)
     SELECT  = build_inner_select_unary O(L) T gates (Sec. III A)
     QSP sequence and walk_operator structure unchanged.
   Self-contained: does not call the original build_qubitization_circuit.
   coeffs    : list of |alpha_j| Hamiltonian coefficients
   lp        : Hamiltonian lowprog (L Pauli terms)
   tau       : rescaled time parameter
   err       : target approximation error
   n_anc     : LCU ancilla register size = ceil(log2 L)
   aux       : scratch qubit for reflect_ancilla
   amp_m     : amplitude precision in bits
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
  let lam      := fold_left Rplus coeffs 0%R in
  let PREP     := build_inner_prep_qrom coeffs lam n_anc amp_m
                    qrom_out qrom_root qrom_pancs in
  let SEL      := build_inner_select_unary lp n_anc (length lp)
                    sel_root sel_pancs in
  let W        := walk_operator PREP SEL n_anc aux in
  let d        := findDegree_qsp tau err in
  let prep_dag := invert PREP in
  useq PREP (useq (qsp_sequence d W (aux + 1)) prep_dag).


(* Heisenberg-limited PEA for qubitization (Babbush et al. Sec. II B).
   Replaces qsp_sequence with QPE on W, achieving O(lambda/epsilon) queries
   vs O((lambda/epsilon) log(1/epsilon)) for QSP.
   m        : number of PEA control qubits; 2^m total W applications
   pea_base : first PEA control qubit
   pea_anc  : ancilla qubit for prepare_chi
   All other parameters same as build_qubitization_circuit_opt. *)
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