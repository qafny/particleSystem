(* ================= Generalized LCU-Taylor in Rcoq ================= *)
Require Import Rcoq.QArith.
Require Import Rcoq.QMatrix.
Require Import Rcoq.QuantumOps.
Require Import Rcoq.QuantumSimulator.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Q_scope.

(* ---------- User-Defined Parameters ---------- *)

Variable n_qubits : nat.                        (* number of qubits in system *)
Variable L : nat.                               (* number of Hamiltonian terms *)
Variable H_list : nat -> SquareMatrix Q (2^n_qubits).  (* Hamiltonian unitaries H_j *)
Variable beta_list : nat -> Q.                  (* Coefficients beta_j *)
Variable psi : Vector Q.                        (* Initial state *)
Variable t : Q.                                 (* Evolution time *)
Variable K : nat.                               (* Taylor series truncation *)
Variable max_retries : nat.                     (* Amplitude amplification retries *)
Variable ancilla_idx : nat.                     (* Ancilla qubit index for control *)

(* ---------------- Utility Functions ---------------- *)

(* Factorial in Q *)
Fixpoint factorial (n : nat) : Q :=
  match n with
  | 0 => 1
  | S k => inject_Z (Z_of_nat (S k)) * factorial k
  end.

(* Taylor coefficient: (-i t)^k / k! *)
Definition taylor_coeff (k : nat) (t : Q) : Q :=
  ((0 - 1 * I * t) ^ k) / factorial k.

(* Generate all sequences of length k over n elements *)
Fixpoint sequences (k n : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      let prev := sequences k' n in
      concat (map (fun seq => map (fun i => i :: seq) (seq 0 n)) prev)
  end.

(* LCU term: product of unitaries according to sequence *)
Definition lcu_term (seq : list nat) : SquareMatrix Q (2^n_qubits) :=
  fold_left (fun acc idx => acc * H_list idx) seq (id_matrix (2^n_qubits)).

(* LCU coefficient: product of beta_j's * Taylor coefficient *)
Definition lcu_coeff (seq : list nat) (k : nat) (t : Q) : Q :=
  let prod_beta := fold_left (fun acc idx => acc * beta_list idx) seq 1 in
  taylor_coeff k t * prod_beta.

(* Prepare ancilla register (normalized) *)
Definition prepare_ancilla (coeffs : list Q) : Vector Q :=
  normalize (map sqrt coeffs).

(* Controlled application of a unitary *)
Definition controlled_apply (U : SquareMatrix Q (2^n_qubits)) (psi : Vector Q) : Vector Q :=
  apply_controlled_unitary ancilla_idx U psi.

(* Amplitude amplification / retry for post-selection *)
Fixpoint amplitude_amplification (psi : Vector Q)
                                 (U_list : list (SquareMatrix Q (2^n_qubits)))
                                 (coeffs : list Q)
                                 (retries : nat) : option (Vector Q) :=
  match retries with
  | 0 => None
  | S r =>
      let psi' := fold_left2 controlled_apply U_list (prepare_ancilla coeffs) psi in
      if measure ancilla_idx psi' = 0 then Some psi'
      else amplitude_amplification psi' U_list coeffs r
  end.

(* ---------------- Main LCU-Taylor Evolution ---------------- *)

Definition lcu_taylor_evolution (psi : Vector Q) (t : Q) (K : nat) : option (Vector Q) :=
  let terms :=
      concat (
        map (fun k => map (fun seq => (lcu_coeff seq k t, lcu_term seq)) (sequences k L))
            (seq 0 K)
      ) in
  let coeffs := map fst terms in
  let unitaries := map snd terms in
  amplitude_amplification psi unitaries coeffs max_retries.

(* ================= OCaml Extraction ================= *)

Require Extraction.
Require Import ExtrOCamlBasic.
Require Import ExtrOCamlString.

(* Extract rational arithmetic to OCaml floats *)
Extract Inlined Constant Qplus => "( +. )".
Extract Inlined Constant Qmult => "( *. )".
Extract Inlined Constant Qminus => "( -. )".
Extract Inlined Constant Qdiv => "( /. )".
Extract Inlined Constant Qeq_bool => "( = )".
Extract Inlined Constant Qlt_bool => "( < )".

(* Extract the main function to OCaml *)
Extraction "lcu_taylor.ml" lcu_taylor_evolution sequences lcu_coeff lcu_term factorial prepare_ancilla amplitude_amplification controlled_apply.