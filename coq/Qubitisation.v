(* QBlueQubitisationHigh.v – Qubitisation for second-quantised Hamiltonians *)

From SQIR Require Import ExtractionGateSet.
Require Import Reals List.
Import ListNotations.
Require Import QBlueSyntax.
Require Import QBlueParTransJwt.

Open Scope R_scope.

(* ===================================================== *)
(* 1. Adjoint of gates and circuits                      *)
(* ===================================================== *)

Definition inv_gate (g : Gate) : Gate :=
  match g with
  | H q => H q | X q => X q | Y q => Y q | Z q => Z q
  | CNOT (c, t) => CNOT (c, t) | CZ (c, t) => CZ (c, t)
  | Rz (theta, q) => Rz (-theta, q)
  | CRz (theta, c, q) => CRz (-theta, c, q)
  | _ => g
  end.

Fixpoint dagger_ucom (c : ucom ExtractionGateSet.U) : ucom ExtractionGateSet.U :=
  match c with
  | SKIP => SKIP
  | USEQ g rest => USEQ (dagger_ucom rest) (inv_gate g)
  end.

(* ===================================================== *)
(* 2. Reflection R = I - 2|0...0⟩⟨0...0| on n ancillas  *)
(*    Uses one extra aux qubit (must start and end at |0⟩) *)
(* ===================================================== *)

Definition reflect_ancilla (n : nat) (aux : nat) : ucom ExtractionGateSet.U :=
  match n with
  | 0 => SKIP
  | _ =>
      let anc := seq 0 n in
      let flip1 := fold_left (fun acc i => USEQ (X i) acc) anc SKIP in
      let compute_and := fold_left (fun acc i => USEQ (CNOT (i, aux)) acc) anc SKIP in
      let apply_z := USEQ (Z aux) SKIP in
      let uncompute_and := fold_left (fun acc i => USEQ (CNOT (i, aux)) acc) (rev anc) SKIP in
      let flip2 := fold_left (fun acc i => USEQ (X i) acc) anc SKIP in
      ucom_app flip1 (ucom_app compute_and 
                (ucom_app apply_z (ucom_app uncompute_and flip2)))
  end.

(* ===================================================== *)
(* 3. Qubitisation walk operator                         *)
(*    Standard form: W = - R U R U†                      *)
(*    (Corrected from previous W = R U)                  *)
(* ===================================================== *)

Definition qubitisation_walk (Ucirc : ucom ExtractionGateSet.U) (n_anc : nat) (aux : nat)
  : ucom ExtractionGateSet.U :=
  let R := reflect_ancilla n_anc aux in
  let Ud := dagger_ucom Ucirc in
  ucom_app R (ucom_app Ucirc (ucom_app R Ud)).

(* ===================================================== *)
(* 4. Quantum Signal Processing (QSP)                    *)
(* ===================================================== *)

Fixpoint qsp_sequence (phases : list R) (signal : nat) (W : ucom ExtractionGateSet.U)
  : ucom ExtractionGateSet.U :=
  match phases with
  | [] => SKIP
  | phi :: phis =>
      let rot := USEQ (Rz (phi, signal)) SKIP in
      ucom_app rot (ucom_app W (qsp_sequence phis signal W))
  end.

(* ===================================================== *)
(* 5. Full evolution circuit                             *)
(* ===================================================== *)

Definition Qubitisation_Evolution
    (circ_seg : ucom ExtractionGateSet.U) (n_anc : nat) (aux : nat) (phases : list R)
    : ucom ExtractionGateSet.U :=
  let W := qubitisation_walk circ_seg n_anc aux in
  qsp_sequence phases aux W.

(* ===================================================== *)
(* 6. High-level interface                               *)
(* ===================================================== *)

Definition Qubitisation_High (err t : R) (nbit : nat) (H : highprog) (phases : list R)
  : ucom ExtractionGateSet.U :=
  let low := highprog_to_lowprog H nbit in
  let nseg := get_nseg t low in
  let k := findK err t low in
  let prog_seg := taylor_exp (t / INR nseg) nbit k low in
  let circ_seg := build_circuit_seg nbit prog_seg in
  let nterm := length prog_seg in
  let n_anc := Nat.log2_up nterm in
  let aux := nbit + n_anc in
  Qubitisation_Evolution circ_seg n_anc aux phases.