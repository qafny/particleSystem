(* QBlueQROM.v — QROM and unary iteration SELECT primitives *)
(* NEW FILE. Babbush et al. PRX 8, 041015 (2018), Sections III A and III C/D. *)
(* Shared foundation used by QBlueTTS, QBlueQuantumWalk, and QBlueQubitization. *)
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSynthDigital.
Require Import QBlue.QBlueQuantumWalk.


(* Use Babbush et al. PRX 8, 041015 (2018):
   Section III A  — unary iteration SELECT: O(L log L) -> O(L) T gates.
   Section III C/D — QROM PREPARE: 4L - 4 T gates, independent of word length. *)


(* Toffoli(NOT ctrl, parent -> child): child = parent AND NOT ctrl. O(1) T. *)
Definition toffoli_neg (ctrl parent child : nat) : ucom ExtractionGateSet.U :=
  useq (X ctrl)
    (useq (control ctrl (control parent (X child)))
          (X ctrl)).

(* Toffoli(ctrl, parent -> child): child = parent AND ctrl. O(1) T. *)
Definition toffoli_pos (ctrl parent child : nat) : ucom ExtractionGateSet.U :=
  control ctrl (control parent (X child)).


(* Depth-first unary iteration tree (Babbush et al. Section III A).
   Left child  indicator = parent AND NOT ctrl_bit  (toffoli_neg).
   Right child indicator = parent AND     ctrl_bit  (toffoli_pos).
   Leaf: apply (op idx) singly controlled on the leaf indicator.
   Total: O(L) Toffoli = O(L) T gates for all L = 2^nqcn terms.
   Requires nqcn path ancilla qubits (one per level) + 1 root ancilla. *)
Fixpoint dfs_select (fuel depth nqcn ctrl_base : nat)
    (path_ancs : list nat) (parent_q leaf_start : nat)
    (op : nat -> ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  match fuel with
  | O => SKIP
  | S fuel' =>
      if depth =? nqcn then
        control parent_q (op leaf_start)
      else
        let ctrl_q    := ctrl_base + depth in
        let my_anc    := nth depth path_ancs 0 in
        let half      := Nat.pow 2 (nqcn - depth - 1) in
        let load_l    := toffoli_neg ctrl_q parent_q my_anc in
        let left_sub  := dfs_select fuel' (S depth) nqcn ctrl_base
                           path_ancs my_anc leaf_start op in
        let unload_l  := toffoli_neg ctrl_q parent_q my_anc in
        let load_r    := toffoli_pos ctrl_q parent_q my_anc in
        let right_sub := dfs_select fuel' (S depth) nqcn ctrl_base
                           path_ancs my_anc (leaf_start + half) op in
        let unload_r  := toffoli_pos ctrl_q parent_q my_anc in
        useq load_l
          (useq left_sub
            (useq unload_l
              (useq load_r
                (useq right_sub unload_r))))
  end.

(* Full unary iteration SELECT.
   root_q    : ancilla for root indicator (initialised |0> -> |1> -> |0>)
   path_ancs : nqcn ancilla qubits, one per tree level
   L, nqcn   : number of terms and number of index qubits
   ctrl_base : index of the first (MSB) control qubit *)
Definition unary_iter_select (L nqcn ctrl_base root_q : nat)
    (path_ancs : list nat)
    (op : nat -> ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  useq (X root_q)
    (useq (dfs_select (L + 1) 0 nqcn ctrl_base path_ancs root_q 0 op)
          (X root_q)).


(* QROM data loading (Babbush et al. Section III C).
   db[idx] = list of output qubit offsets to XOR into the output register
   when the index register holds |idx>.
   Uses unary_iter_select for O(L) = 4L-4 T gates total. *)
Definition qrom_load (db : list (list nat)) (nqcn ctrl_base out_base root_q : nat)
    (path_ancs : list nat) : ucom ExtractionGateSet.U :=
  unary_iter_select (length db) nqcn ctrl_base root_q path_ancs
    (fun idx =>
      fold_left (fun acc q => useq acc (X (out_base + q)))
        (nth idx db []) SKIP).

(* Encode a list of amplitudes as fixed-point bit-strings for QROM loading.
   amp_m bits per entry: mu = round(amp * 2^amp_m). *)
Definition encode_amps_as_bits (amps : list R) (amp_m : nat) : list (list nat) :=
  let scale := INR (Nat.pow 2 amp_m) in
  map (fun a =>
    let mu := Z.to_nat (up (a * scale)) in
    filter (fun j => Nat.land (Nat.shiftr mu j) 1 =? 1) (seq 0 amp_m)
  ) amps.

(* QROM PREPARE (Babbush et al. Section III D).
   T complexity: 4L - 4 T gates from QROM data loading,
   independent of amp_m (word length).
   Compare: direct rotation synthesis costs O(L * amp_m) T gates.
   amps      : normalised amplitude list (length = 2^nqcn, L2-normalised)
   nqcn      : number of index qubits
   amp_m     : amplitude precision in bits
   ctrl_base : first index qubit
   out_base  : first QROM output qubit (amp_m qubits allocated here)
   root_q    : QROM root indicator ancilla
   path_ancs : nqcn QROM path ancilla qubits *)
Definition qrom_prepare (nqcn amp_m ctrl_base out_base root_q : nat)
    (path_ancs : list nat) (amps : list R)
    : ucom ExtractionGateSet.U :=
  let db  := encode_amps_as_bits amps amp_m in
  let had := fold_left
               (fun acc i => useq acc (H (ctrl_base + i)))
               (seq 0 nqcn) SKIP in
  useq had (qrom_load db nqcn ctrl_base out_base root_q path_ancs).

(* Extract L2-normalised amplitudes from a lowprog for use with qrom_prepare. *)
Definition lowprog_to_amps (lp : lowprog) : list R :=
  let mags   := map (fun x => Cmod (fst x)) lp in
  let lambda := fold_left Rplus mags 0%R in
  map (fun m => sqrt (m / lambda)) mags.