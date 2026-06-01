(* QBluePEA.v — Heisenberg-limited phase estimation *)
(* NEW FILE. Babbush et al. PRX 8, 041015 (2018), Section II B and Figure 2. *)
(* Shared by QBlueTTS, QBlueQuantumWalk, and QBlueQubitization. *)
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Require Import QBlue.QBlueQuantumWalk.


(* Use Babbush et al. PRX 8, 041015 (2018), Section II B:
   Standard QPE needs 2^m controlled-W applications to resolve eigenphases
   to precision 2pi/2^m.  Heisenberg PEA achieves the same precision using
   the resource state chi_m and reaches the Heisenberg limit O(lambda/epsilon).
   Total W applications: 2^m (same count as standard QPE, better constant). *)


(* Inverse QFT on m qubits at ctrl_base..ctrl_base+m-1.
   Applied at the end of the PEA readout circuit. *)
Fixpoint qft_dagger_step (q : nat) (ctrls : list nat)
    : ucom ExtractionGateSet.U :=
  match ctrls with
  | []        => H q
  | c :: rest =>
      let angle := (- PI / INR (Nat.pow 2 (length ctrls + 1)))%R in
      useq (control c (U1 angle q)) (qft_dagger_step q rest)
  end.

Fixpoint qft_dagger (m ctrl_base : nat) : ucom ExtractionGateSet.U :=
  match m with
  | O    => SKIP
  | S m' =>
      let q     := ctrl_base + m' in
      let ctrls := rev (seq ctrl_base m') in
      useq (qft_dagger_step q ctrls) (qft_dagger m' ctrl_base)
  end.


(* Resource state chi_m (Babbush et al. Eq. 17):
   |chi_m> = sqrt(2/(2^m+1)) sum_{n=0}^{2^m-1} sin(pi(n+1)/(2^m+1)) |n>
   Prepared on m qubits at ctrl_base using one ancilla anc_q.
   Circuit: H on m+1 qubits, controlled U1 rotations, H on anc_q. *)
Definition prepare_chi (m ctrl_base anc_q : nat) : ucom ExtractionGateSet.U :=
  let had_ctrl := fold_left
                    (fun acc i => useq acc (H (ctrl_base + i)))
                    (seq 0 m) SKIP in
  let had_anc  := H anc_q in
  let rots     := fold_left (fun acc k =>
                    let angle := (PI * INR (Nat.pow 2 k)
                                  / INR (Nat.pow 2 m + 1))%R in
                    useq acc (control (ctrl_base + k) (U1 angle anc_q))
                  ) (seq 0 m) SKIP in
  let init_rot := U1 (PI / INR (Nat.pow 2 m + 1))%R anc_q in
  useq had_ctrl
    (useq had_anc
      (useq rots
        (useq init_rot (H anc_q)))).


(* Heisenberg-limited PEA (Babbush et al. Figure 2).
   Wraps any walk operator W for Hamiltonian phase estimation.
   Uses chi_m instead of uniform superposition, giving Heisenberg-limit
   query complexity O(lambda/epsilon) rather than O((lambda/epsilon) log(1/epsilon)).
   W         : walk operator ucom (from walk_operator or build_qubitization_circuit)
   m         : number of PEA control qubits; 2^m total W applications
   ctrl_base : first PEA control qubit
   anc_q     : ancilla qubit for prepare_chi *)
Definition heis_pea (m ctrl_base anc_q : nat)
    (W : ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  let chi      := prepare_chi m ctrl_base anc_q in
  let walk_ops := fold_left (fun acc k =>
                    let W_pow := n_copies (Nat.pow 2 k) W in
                    useq acc (control (ctrl_base + k) W_pow)
                  ) (seq 0 m) SKIP in
  let iqft     := qft_dagger m ctrl_base in
  useq chi (useq walk_ops iqft).


(* Convenience wrapper: build W from PREP and SELECT, then run Heisenberg PEA.
   PREP    : PREPARE circuit
   SELECT  : SELECT circuit
   n_anc   : number of ancilla qubits in the LCU ancilla register
   aux     : scratch qubit index for reflect_ancilla *)
Definition heis_pea_from_lcu (m ctrl_base anc_q n_anc aux : nat)
    (PREP SELECT : ucom ExtractionGateSet.U)
    : ucom ExtractionGateSet.U :=
  let W := walk_operator PREP SELECT n_anc aux in
  heis_pea m ctrl_base anc_q W.