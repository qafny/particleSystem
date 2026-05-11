(*************************************************************************)
(* QBlueQuantumWalk.v                                                    *)
(* Quantum Walk LCU                        *)
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