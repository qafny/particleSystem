(*************************************************************************)
(* QBlueQuantumWalk_opt.v                                                *)
(* QBlueQuantumWalk unchanged + optimisations from                       *)
(* Babbush et al. PRX 8, 041015 (2018), Sections II B, III A, III C/D.  *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Parameter bessel_j : nat -> R -> R.
Parameter findK_qwalk : R -> R -> nat.

Section QWalkCircuit.

Fixpoint list_norm_sq (l : list R) : R :=
  match l with
  | []      => R0
  | x :: tl => x * x + list_norm_sq tl
  end.

(* Maps |0...0> -> sum_k amps[k] |k> via recursive Schmidt decomposition.
   Requires: length amps = 2^(length qubits), |amps|_2 = 1, MSB-first. *)
Fixpoint build_state_prep (amps : list R) (qubits : list nat)
    : ucom ExtractionGateSet.U :=
  match qubits with
  | []  => SKIP
  | [q] =>
      let a1 := match amps with
                | _ :: a :: _ => a
                | _           => R0
                end in
      U3 (2 * asin a1)%R R0 R0 q
  | msb :: rest =>
      let n_rest  := length rest in
      let half    := Nat.pow 2 n_rest in
      let left    := firstn half amps in
      let right   := skipn  half amps in
      let nl      := sqrt (list_norm_sq left)  in
      let nr      := sqrt (list_norm_sq right) in
      let tot     := sqrt (nl * nl + nr * nr)%R in
      let eps_r   := (1 / 1000000)%R in
      let theta   :=
        if Rlt_dec eps_r tot
        then (2 * asin (nr / tot))%R
        else R0 in
      let left_n  :=
        if Rlt_dec eps_r nl
        then map (fun x => (x / nl)%R) left
        else left in
      let right_n :=
        if Rlt_dec eps_r nr
        then map (fun x => (x / nr)%R) right
        else right in
      let sub_l := build_state_prep left_n  rest in
      let sub_r := build_state_prep right_n rest in
      useq (U3 theta R0 R0 msb)
      (useq (ExtractionGateSet.control msb sub_r)
      (useq (X msb)
      (useq (ExtractionGateSet.control msb sub_l)
            (X msb))))
  end.

(* PREP|0> = sum_j sqrt(alpha_j / lambda) |j> *)
Definition build_inner_prep (coeffs : list R) (lam : R) (n_anc : nat)
    : ucom ExtractionGateSet.U :=
  let sqrt_amps := map (fun a => sqrt (a / lam)) coeffs in
  let qubits    := rev (seq 0 n_anc) in
  build_state_prep sqrt_amps qubits.

(* PREP|0> = sum_{k=0}^{K} sqrt(|J_k(tau)|) |k> *)
Definition build_outer_prep
    (tau : R) (k_trunc qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  let bessel_amps :=
    map (fun k => sqrt (Rabs (bessel_j k tau))) (seq 0 (S k_trunc)) in
  let qubits := rev (seq qubit_offset n_outer) in
  build_state_prep bessel_amps qubits.

(* 2|0...0><0...0| - I on qubits 0..n-1. aux is a scratch qubit >= n. *)
Definition reflect_ancilla (n : nat) (aux : nat) : ucom ExtractionGateSet.U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz :=
    fold_right (fun i acc => ExtractionGateSet.control i acc) (U1 PI aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* W = R_G . R_Pi  (Berry 2015 Eq. 3)
   R_G  = PREP^dag . R0 . PREP
   R_Pi = U^dag   . R0 . U      where U = PREP . SELECT *)
Definition walk_operator
    (PREP SELECT : ucom ExtractionGateSet.U)
    (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let R0       := reflect_ancilla n_anc aux in
  let PREP_dag := invert PREP in
  let U        := useq PREP SELECT in
  let U_dag    := invert U in
  let R_G      := useq (useq PREP_dag R0) PREP in
  let R_Pi     := useq (useq U_dag    R0) U    in
  useq R_G R_Pi.

Fixpoint n_copies (n : nat) (g : ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  match n with
  | O    => SKIP
  | S n' => useq g (n_copies n' g)
  end.

(* For each k where J_k(tau) < 0, applies phase -1 to |k> on the outer register. *)
Definition apply_bessel_signs
    (tau : R) (K qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  fold_left (fun acc k =>
    if Rlt_dec (bessel_j k tau) R0
    then
      let anc := seq qubit_offset n_outer in
      let pre := fold_left (fun c j =>
                   if Nat.testbit k (j - qubit_offset)
                   then c
                   else useq c (X j)
                 ) anc SKIP in
      let phase_circ :=
        match anc with
        | []          => SKIP
        | [q]         => useq (X q) (useq (U1 PI q) (X q))
        | q_lsb :: rest =>
            fold_right
              (fun j s => ExtractionGateSet.control j s)
              (U1 PI q_lsb)
              rest
        end in
      useq acc (useq pre (useq phase_circ pre))
    else acc
  ) (seq 0 (S K)) SKIP.

(* Applies (-i)^k phase to the outer register via U1(-pi*2^j/2) on each qubit j. *)
Definition apply_complex_phases
    (qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  fold_left (fun acc j =>
    let pow2 := Nat.pow 2 j in
    useq acc (U1 (-(PI / 2 * INR pow2))%R (qubit_offset + j))
  ) (seq 0 n_outer) SKIP.

(* Full Berry 2015 circuit:
     full_prep = outer_prep . complex_phases . sign_phases
     output    = full_prep . sel_outer . full_prep^dag
   sel_outer uses binary decomposition: W^k = prod_j (W^{2^j})^{q_j}. *)
Definition build_qwalk_lcu_circuit
    (inner_prep select outer_prep : ucom ExtractionGateSet.U)
    (tau : R) (n_anc aux K qubit_offset n_outer : nat)
    : ucom ExtractionGateSet.U :=
  let W              := walk_operator inner_prep select n_anc aux in
  let complex_phases := apply_complex_phases qubit_offset n_outer in
  let sign_phases    := apply_bessel_signs tau K qubit_offset n_outer in
  let full_prep      := useq outer_prep (useq complex_phases sign_phases) in
  let full_unp       := invert full_prep in
  let sel_outer      :=
    fold_left (fun acc j =>
      let pow2  := Nat.pow 2 j in
      let W_pow := n_copies pow2 W in
      useq acc (ExtractionGateSet.control (qubit_offset + j) W_pow)
    ) (seq 0 n_outer) SKIP in
  useq full_prep (useq sel_outer full_unp).

End QWalkCircuit.


(* ------------------------------------------------------------------ *)
(* ADDED: optimisations from Babbush et al. PRX 8, 041015 (2018).     *)
(* Requires QBlue.QBlueQROM and QBlue.QBluePEA to be compiled first. *)
(* ------------------------------------------------------------------ *)
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSynthDigital.

(* ADDED: QROM-based inner PREPARE (Babbush et al. Sec. III C/D).
   Replaces build_inner_prep (which uses build_state_prep = O(L*amp_m) T).
   T complexity: O(L) = 4L-4 T gates from QROM data loading.
   coeffs     : list of |alpha_j| Hamiltonian coefficients
   lam        : their sum (lambda = 1-norm)
   n_anc      : number of inner ancilla qubits = ceil(log2 L)
   amp_m      : amplitude precision in bits
   out_base   : first QROM output qubit
   root_q     : QROM root indicator ancilla
   path_ancs  : n_anc QROM path ancilla qubits *)
Definition build_inner_prep_qrom
    (coeffs : list R) (lam : R) (n_anc amp_m out_base root_q : nat)
    (path_ancs : list nat)
    : ucom ExtractionGateSet.U :=
  let amps := map (fun a => sqrt (a / lam)) coeffs in
  qrom_prepare n_anc amp_m 0 out_base root_q path_ancs amps.

(* ADDED: QROM-based outer PREPARE (Babbush et al. Sec. III C/D).
   Replaces build_outer_prep (which uses build_state_prep = O(K*amp_m) T).
   T complexity: O(K) = 4K-4 T gates from QROM data loading.
   tau         : rescaled time parameter (lambda * t / r)
   k_trunc     : truncation order K
   qubit_offset: first outer ancilla qubit
   n_outer     : number of outer ancilla qubits
   amp_m       : amplitude precision in bits
   out_base    : first QROM output qubit
   root_q      : QROM root indicator ancilla
   path_ancs   : n_outer QROM path ancilla qubits *)
Definition build_outer_prep_qrom
    (tau : R) (k_trunc qubit_offset n_outer amp_m out_base root_q : nat)
    (path_ancs : list nat)
    : ucom ExtractionGateSet.U :=
  let amps := map (fun k => sqrt (Rabs (bessel_j k tau)))
                (seq 0 (S k_trunc)) in
  qrom_prepare n_outer amp_m qubit_offset out_base root_q path_ancs amps.

(* ADDED: unary iteration inner SELECT (Babbush et al. Sec. III A).
   Replaces the fold_left build_cntlV SELECT in translate_lowp2circ_qwalk,
   reducing T complexity from O(L log L) to O(L).
   lp         : Hamiltonian lowprog (L terms)
   n_inner    : number of inner ancilla qubits = ceil(log2 L)
   nqv        : number of system qubits
   root_q     : SELECT tree root ancilla
   path_ancs  : n_inner SELECT tree path ancilla qubits *)
Definition build_inner_select_unary
    (lp : lowprog) (n_inner nqv root_q : nat)
    (path_ancs : list nat)
    : ucom ExtractionGateSet.U :=
  let L := length lp in
  unary_iter_select L n_inner 0 root_q path_ancs
    (fun idx =>
      match nth_error lp idx with
      | None          => ExtractionGateSet.SKIP
      | Some (amp, f) =>
          synth_digital_ibm_apauli (fst amp) (n_inner + nqv) f
      end).

(* ADDED: optimised quantum walk LCU circuit.
   Replaces build_qwalk_lcu_circuit using:
     inner PREP  = build_inner_prep_qrom (O(L) T)
     inner SELECT = build_inner_select_unary (O(L) T)
     outer PREP  = build_outer_prep_qrom (O(K) T)
     outer SELECT = binary decomposition sel_outer (unchanged, already O(n_outer))
   All other components (walk_operator, phases, signs) unchanged.
   amp_m      : amplitude precision in bits
   qrom_out_i : first QROM output qubit for inner PREP
   qrom_ri    : QROM root ancilla for inner PREP
   qrom_pi    : n_anc QROM path ancillae for inner PREP
   sel_root   : SELECT tree root ancilla
   sel_pancs  : n_anc SELECT tree path ancillae
   qrom_out_o : first QROM output qubit for outer PREP
   qrom_ro    : QROM root ancilla for outer PREP
   qrom_po    : n_outer QROM path ancillae for outer PREP *)
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
  build_qwalk_lcu_circuit inner_PREP inner_SEL outer_PREP
    tau n_anc aux K qubit_offset n_outer.

(* ADDED: Heisenberg-limited PEA for quantum walk (Babbush et al. Sec. II B).
   Replaces the standard QPE that would wrap build_qwalk_lcu_circuit.
   Uses heis_pea_from_lcu with the optimised PREP and SELECT.
   m          : number of PEA control qubits
   pea_base   : first PEA control qubit
   pea_anc    : ancilla for prepare_chi
   n_anc      : LCU ancilla register size
   refl_aux   : scratch qubit for reflect_ancilla *)
Definition build_qwalk_heis_pea
    (coeffs : list R) (lp : lowprog)
    (n_anc aux m pea_base pea_anc amp_m : nat)
    (qrom_out_i qrom_ri sel_root : nat)
    (qrom_pi sel_pancs : list nat)
    : ucom ExtractionGateSet.U :=
  let lam  := fold_left Rplus coeffs 0%R in
  let PREP := build_inner_prep_qrom coeffs lam n_anc amp_m
                qrom_out_i qrom_ri qrom_pi in
  let SEL  := build_inner_select_unary lp n_anc
                (length lp) sel_root sel_pancs in
  heis_pea_from_lcu m pea_base pea_anc n_anc aux PREP SEL.