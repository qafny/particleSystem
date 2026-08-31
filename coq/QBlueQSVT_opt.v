(* QBlueQSVT_opt.v — QSVT with PRX optimisations *)
(* Babbush et al. PRX 8, 041015 (2018), Sections II B, III A, III C/D *)
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.
Require Import QBlue.QBlueQuantumWalk_opt.


(* Use Babbush et al. PRX 8, 041015 (2018):
   QSVT uses block-encoding SELECT oracle directly (no walk operator step).
   Optimisations applied:
     PREPARE = build_inner_prep_qrom  O(L) T  (Sec. III C/D)
     SELECT  = build_inner_select_unary O(L) T (Sec. III A)
     Heisenberg PEA as alternative to polynomial QSVT (Sec. II B) *)


(* Projector-controlled phase shift on n ancilla qubits.
   aux is a scratch qubit; phi is the phase angle. *)
Definition reflect_ancilla_phase (n aux : nat) (phi : R)
    : ucom ExtractionGateSet.U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz := fold_right (fun i acc => control i acc) (U1 phi aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* QSVT sequence: alternates phase shifts and SELECT applications.
   For degree d: d+1 phase shifts, d SELECT applications.
   Phase values are R0 placeholders; exact angles computed at extraction. *)
Fixpoint qsvt_sequence (d : nat) (select : ucom ExtractionGateSet.U) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  match d with
  | O    => reflect_ancilla_phase n_anc aux R0
  | S d' => useq (reflect_ancilla_phase n_anc aux R0)
                 (useq select (qsvt_sequence d' select n_anc aux))
  end.

(* QSVT polynomial degree: d = 2K+1 where K = truncation from findK_qwalk *)
Definition findDegree_qsvt (tau err : R) : nat :=
  2 * findK_qwalk tau err + 1.


(* Optimised QSVT circuit (Babbush et al. PRX 2018):
     PREPARE = build_inner_prep_qrom    O(L) T  (Sec. III C/D)
     SELECT  = build_inner_select_unary O(L) T  (Sec. III A)
     QSVT sequence structure unchanged.
   Self-contained: does not call the original build_qsvt_circuit.
   coeffs    : list of |alpha_j| Hamiltonian coefficients
   lp        : Hamiltonian lowprog (L Pauli terms)
   tau       : rescaled time parameter
   err       : target approximation error
   n_anc     : LCU ancilla register size = ceil(log2 L)
   aux       : scratch qubit for reflect_ancilla_phase
   amp_m     : amplitude precision in bits
   qrom_out  : first QROM output qubit
   qrom_root : QROM root indicator ancilla
   qrom_pancs: n_anc QROM path ancilla qubits
   sel_root  : SELECT tree root ancilla
   sel_pancs : n_anc SELECT tree path ancilla qubits *)
Definition build_qsvt_circuit_opt
    (coeffs : list R) (lp : lowprog)
    (tau err : R) (n_anc aux amp_m qrom_out qrom_root sel_root : nat)
    (qrom_pancs sel_pancs : list nat)
    : ucom ExtractionGateSet.U :=
  let lam      := fold_left Rplus coeffs 0%R in
  let PREP     := build_inner_prep_qrom coeffs lam n_anc amp_m
                    qrom_out qrom_root qrom_pancs in
  let SEL      := build_inner_select_unary lp n_anc (length lp)
                    sel_root sel_pancs in
  let d        := findDegree_qsvt tau err in
  let prep_dag := invert PREP in
  useq PREP (useq (qsvt_sequence d SEL n_anc aux) prep_dag).


(* Heisenberg-limited PEA for QSVT (Babbush et al. Sec. II B).
   Alternative to polynomial QSVT: performs QPE on the walk operator W
   built from PREP and SELECT, achieving O(lambda/epsilon) queries
   vs O((lambda/epsilon) log(1/epsilon)) for polynomial QSVT.
   Uses QROM PREPARE and unary iteration SELECT throughout.
   m        : number of PEA control qubits; 2^m total W applications
   pea_base : first PEA control qubit
   pea_anc  : ancilla qubit for prepare_chi
   All other parameters same as build_qsvt_circuit_opt. *)
Definition build_qsvt_heis_pea
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
