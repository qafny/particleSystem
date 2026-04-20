(* QBlueQubitisationHigh.v – Qubitisation for second-quantised Hamiltonians (standalone) *)
From SQIR Require Import ExtractionGateSet.
Require Import Reals List.
Import ListNotations.
Require Import QBlueSyntax.
Require Import QBlueParTransJwt.      (* Jordan-Wigner: highprog_to_lowprog *)
Require Import QBlueTTS.              (* Taylor series: taylor_exp, findK, get_nseg, build_circuit_seg *)

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* 1. Adjoint (dagger) of a gate and of a ucom circuit               *)
(* ------------------------------------------------------------------ *)

Definition inv_gate (g : Gate) : Gate :=
  match g with
  | H q => H q
  | X q => X q
  | Y q => Y q
  | Z q => Z q
  | CNOT (c, t) => CNOT (c, t)
  | CZ (c, t) => CZ (c, t)
  | Rz (theta, q) => Rz (-theta, q)
  | CRz (theta, c, q) => CRz (-theta, c, q)
  | _ => g   (* extend if more gates appear *)
  end.

Fixpoint dagger_ucom (c : ucom ExtractionGateSet.U) : ucom ExtractionGateSet.U :=
  match c with
  | SKIP => SKIP
  | USEQ g rest => USEQ (dagger_ucom rest) (inv_gate g)
  end.

(* ------------------------------------------------------------------ *)
(* 2. Reflection on ancilla qubits: 2|0...0⟩⟨0...0| - I              *)
(* ------------------------------------------------------------------ *)

(* Build a multi-controlled Z using an auxiliary qubit (must be |0⟩).
   ancilla qubits are [0 .. n-1]; aux is an extra qubit (index n). *)
Definition reflect_ancilla (n : nat) (aux : nat) : ucom ExtractionGateSet.U :=
  let anc := seq 0 n in
  let flip1 := fold_left (fun acc i => USEQ (X i) acc) anc SKIP in
  let compute_and := fold_left (fun acc i => USEQ (CNOT (i, aux)) acc) anc SKIP in
  let apply_z := USEQ (Z aux) compute_and in
  let uncompute_and := fold_left (fun acc i => USEQ (CNOT (i, aux)) acc) (rev anc) SKIP in
  let flip2 := fold_left (fun acc i => USEQ (X i) acc) anc SKIP in
  USEQ (USEQ flip1 (USEQ compute_and apply_z)) (USEQ uncompute_and flip2).

(* ------------------------------------------------------------------ *)
(* 3. Quantum walk operator W = R · U · R · U^\dagger                 *)
(* ------------------------------------------------------------------ *)

Definition walk_operator (U : ucom ExtractionGateSet.U) (n_anc : nat) (aux : nat) : ucom ExtractionGateSet.U :=
  let R := reflect_ancilla n_anc aux in
  let Ud := dagger_ucom U in
  USEQ (USEQ (USEQ R U) R) Ud.

(* ------------------------------------------------------------------ *)
(* 4. Qubitisation for low-level Pauli representation (lowprog)      *)
(* ------------------------------------------------------------------ *)

Definition TTS_Qubitisation (err t : R) (nbit : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg := get_nseg t input in
  let k := findK err t input in
  let prog_seg := taylor_exp (t / INR nseg) nbit k input in
  let circ_seg := build_circuit_seg nbit prog_seg in
  let nterm := length prog_seg in
  let n_anc := Nat.log2_up nterm in
  let aux := nbit + n_anc in
  let walk := walk_operator circ_seg n_anc aux in
  fold_left (fun acc _ => USEQ walk acc) (seq 0 nseg) SKIP.

(* ------------------------------------------------------------------ *)
(* 5. Qubitisation for second-quantised Hamiltonians (highprog)      *)
(* ------------------------------------------------------------------ *)

Definition TTS_Qubitisation_high (err t : R) (nbit : nat) (H : highprog) : ucom ExtractionGateSet.U :=
  let low := highprog_to_lowprog H nbit in
  TTS_Qubitisation err t nbit low.