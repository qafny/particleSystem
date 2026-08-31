(* QBlueQuantumWalk_opt.v — Quantum Walk LCU with PRX optimisations only *)
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
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSynthDigital.
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.


(* Bessel function J_k(tau) and walk truncation order: classical parameters *)
Parameter bessel_j   : nat -> R -> R.
Parameter findK_qwalk : R -> R -> nat.


(* Reflection 2|0...0><0...0| - I on qubits 0..n-1; aux is a scratch qubit *)
Definition reflect_ancilla (n aux : nat) : ucom ExtractionGateSet.U :=
  let anc     := seq 0 n in
  let flip1   := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz := fold_right (fun i acc => control i acc) (U1 PI aux) anc in
  let phase   := useq (useq (X aux) multi_cz) (X aux) in
  let flip2   := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* Walk operator W = R_G . R_Pi *)
Definition walk_operator (PREP SELECT : ucom ExtractionGateSet.U) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let R0      := reflect_ancilla n_anc aux in
  let U       := useq PREP SELECT in
  let R_G     := useq (useq (invert PREP) R0) PREP in
  let R_Pi    := useq (useq (invert U)    R0) U    in
  useq R_G R_Pi.

(* n copies of gate g in sequence *)
Fixpoint n_copies (n : nat) (g : ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  match n with
  | O    => SKIP
  | S n' => useq g (n_copies n' g)
  end.

(* Phase correction for negative Bessel coefficients J_k(tau) < 0 *)
Definition apply_bessel_signs (tau : R) (K qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  fold_left (fun acc k =>
    if Rlt_dec (bessel_j k tau) R0
    then
      let anc := seq qubit_offset n_outer in
      let pre := fold_left (fun c j =>
                   if Nat.testbit k (j - qubit_offset) then c
                   else useq c (X j)) anc SKIP in
      let phase_circ :=
        match anc with
        | []           => SKIP
        | [q]          => useq (X q) (useq (U1 PI q) (X q))
        | q_lsb :: rest =>
            fold_right (fun j s => control j s) (U1 PI q_lsb) rest
        end in
      useq acc (useq pre (useq phase_circ pre))
    else acc
  ) (seq 0 (S K)) SKIP.

(* Phase (-i)^k applied to outer register via U1(-pi*2^j/2) on qubit j *)
Definition apply_complex_phases (qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  fold_left (fun acc j =>
    useq acc (U1 (-(PI / 2 * INR (Nat.pow 2 j)))%R (qubit_offset + j))
  ) (seq 0 n_outer) SKIP.


(* QROM inner PREPARE: O(L) T gates (Babbush et al. Sec. III C/D).
   Replaces build_inner_prep which costs O(L * amp_m) T gates.
   coeffs    : list of |alpha_j| Hamiltonian coefficients
   lam       : 1-norm (sum of coeffs)
   n_anc     : ceil(log2 L) inner ancilla qubits
   amp_m     : amplitude precision in bits
   out_base  : first QROM output qubit
   root_q    : QROM root indicator ancilla
   path_ancs : n_anc QROM path ancilla qubits *)
Definition build_inner_prep_qrom
    (coeffs : list R) (lam : R) (n_anc amp_m out_base root_q : nat)
    (path_ancs : list nat) : ucom ExtractionGateSet.U :=
  let amps := map (fun a => sqrt (a / lam)) coeffs in
  qrom_prepare n_anc amp_m 0 out_base root_q path_ancs amps.

(* QROM outer PREPARE: O(K) T gates (Babbush et al. Sec. III C/D).
   Replaces build_outer_prep which costs O(K * amp_m) T gates.
   tau          : rescaled time (lambda * t / r)
   k_trunc      : truncation order K
   qubit_offset : first outer ancilla qubit
   n_outer      : number of outer ancilla qubits
   amp_m        : amplitude precision in bits
   out_base     : first QROM output qubit
   root_q       : QROM root indicator ancilla
   path_ancs    : n_outer QROM path ancilla qubits *)
Definition build_outer_prep_qrom
    (tau : R) (k_trunc qubit_offset n_outer amp_m out_base root_q : nat)
    (path_ancs : list nat) : ucom ExtractionGateSet.U :=
  let amps := map (fun k => sqrt (Rabs (bessel_j k tau))) (seq 0 (S k_trunc)) in
  qrom_prepare n_outer amp_m qubit_offset out_base root_q path_ancs amps.

(* Unary iteration inner SELECT: O(L) T gates (Babbush et al. Sec. III A).
   Replaces fold_left build_cntlV which costs O(L log L) T gates.
   lp        : Hamiltonian lowprog (L Pauli terms)
   n_inner   : ceil(log2 L) inner ancilla qubits
   nqv       : number of system qubits
   root_q    : SELECT tree root ancilla
   path_ancs : n_inner SELECT tree path ancilla qubits *)
Definition build_inner_select_unary
    (lp : lowprog) (n_inner nqv root_q : nat)
    (path_ancs : list nat) : ucom ExtractionGateSet.U :=
  unary_iter_select (length lp) n_inner 0 root_q path_ancs
    (fun idx =>
      match nth_error lp idx with
      | None          => ExtractionGateSet.SKIP
      | Some (amp, f) => synth_digital_ibm_apauli (fst amp) (n_inner + nqv) f
      end).


(* Optimised quantum walk LCU circuit (Babbush et al. PRX 2018):
     inner PREP   = build_inner_prep_qrom  O(L) T  (Sec. III C/D)
     inner SELECT = build_inner_select_unary O(L) T (Sec. III A)
     outer PREP   = build_outer_prep_qrom  O(K) T  (Sec. III C/D)
     outer SELECT = binary decomposition     O(n_outer) (unchanged, already optimal)
   Self-contained: does not call the original build_qwalk_lcu_circuit. *)
Definition build_qwalk_lcu_circuit_opt
    (coeffs : list R) (lp : lowprog)
    (tau : R) (n_anc aux K qubit_offset n_outer amp_m : nat)
    (qrom_out_i qrom_ri sel_root : nat)
    (qrom_pi sel_pancs : list nat)
    (qrom_out_o qrom_ro : nat)
    (qrom_po : list nat)
    : ucom ExtractionGateSet.U :=
  let lam        := fold_left Rplus coeffs 0%R in
  let inner_PREP := build_inner_prep_qrom coeffs lam n_anc amp_m
                      qrom_out_i qrom_ri qrom_pi in
  let inner_SEL  := build_inner_select_unary lp n_anc
                      (qubit_offset - n_anc) sel_root sel_pancs in
  let outer_PREP := build_outer_prep_qrom tau K qubit_offset n_outer amp_m
                      qrom_out_o qrom_ro qrom_po in
  let W          := walk_operator inner_PREP inner_SEL n_anc aux in
  let c_phases   := apply_complex_phases qubit_offset n_outer in
  let s_phases   := apply_bessel_signs tau K qubit_offset n_outer in
  let full_prep  := useq outer_PREP (useq c_phases s_phases) in
  let sel_outer  := fold_left (fun acc j =>
                      useq acc (control (qubit_offset + j) (n_copies (Nat.pow 2 j) W))
                    ) (seq 0 n_outer) SKIP in
  useq full_prep (useq sel_outer (invert full_prep)).


(* Heisenberg-limited PEA for quantum walk (Babbush et al. Sec. II B).
   O(lambda/epsilon) query complexity; saturates Heisenberg limit.
   m          : number of PEA control qubits
   pea_base   : first PEA control qubit
   pea_anc    : ancilla for prepare_chi
   n_anc      : LCU ancilla register size
   refl_aux   : scratch qubit for reflect_ancilla *)
Definition build_qwalk_heis_pea
    (coeffs : list R) (lp : lowprog)
    (n_anc refl_aux m pea_base pea_anc amp_m : nat)
    (qrom_out_i qrom_ri sel_root : nat)
    (qrom_pi sel_pancs : list nat)
    : ucom ExtractionGateSet.U :=
  let lam  := fold_left Rplus coeffs 0%R in
  let PREP := build_inner_prep_qrom coeffs lam n_anc amp_m
                qrom_out_i qrom_ri qrom_pi in
  let SEL  := build_inner_select_unary lp n_anc (length lp)
                sel_root sel_pancs in
  heis_pea_from_lcu m pea_base pea_anc n_anc refl_aux PREP SEL.