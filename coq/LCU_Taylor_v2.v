(* ================= QBlue LCU-Taylor (Pauli formulation) ================= *)

Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope C_scope.

(* ================= Basic QBlue Types ================= *)

Definition pauli := paulimat.

Definition pauli_string := nat -> pauli.

Definition low_term := (C * pauli_string) %type.
Definition lowprog := list low_term.

(* ================= User Inputs ================= *)

Variable n_qubits : nat.

Variable H : lowprog.     (* Hamiltonian: sum_j beta_j P_j *)

Variable psi : list (C * nat -> nat). (* QBlue state *)

Variable t : R.
Variable epsilon : R.

Variable r : nat.   (* Trotter segments *)
Variable K : nat.   (* Taylor truncation *)

(* ================= Pauli multiplication rule ================= *)

Definition pauli_mul (a b : pauli) : (C * pauli) :=
  match a, b with
  | paulii, p => (1%R, p)
  | p, paulii => (1%R, p)

  | paulix, paulix => (1%R, paulii)
  | pauliy, pauliy => (1%R, paulii)
  | pauliz, pauliz => (1%R, paulii)

  | paulix, pauliy => (0 + i)%C, pauliz
  | pauliy, paulix => (0 - i)%C, pauliz

  | pauliy, pauliz => (0 + i)%C, paulix
  | pauliz, pauliy => (0 - i)%C, paulix

  | pauliz, paulix => (0 + i)%C, pauliy
  | paulix, pauliz => (0 - i)%C, pauliy
  end.

(* multiply Pauli strings *)
Fixpoint pauli_string_mul (p q : pauli_string) : pauli_string :=
  fun i => snd (pauli_mul (p i) (q i)).

(* ================= Hamiltonian structure ================= *)

Definition H_term := low_term.

Definition H_coeff (h : low_term) : C := fst h.
Definition H_pauli (h : low_term) : pauli_string := snd h.

(* ================= Commuting grouping placeholder ================= *)
(* (you can plug QBlue commutation graph later) *)

Definition commute (p q : pauli_string) : bool := true.

Fixpoint group_commuting (H : lowprog) : list lowprog :=
  match H with
  | [] => []
  | h :: hs =>
      [h] :: group_commuting hs
  end.

(* ================= Taylor coefficient ================= *)

Fixpoint fact (n : nat) : R :=
  match n with
  | 0 => 1
  | S n' => INR (S n') * fact n'
  end.

Definition taylor_coeff (k : nat) (t : R) : C :=
  ((-1) ^ k * (t ^ k) / fact k)%R.

(* ================= LCU expansion ================= *)

Definition lcu_term (h : low_term) : low_term :=
  h.

Definition scale_term (c : C) (h : low_term) : low_term :=
  (c * fst h, snd h).

(* ================= product of Hamiltonian terms ================= *)

Fixpoint sequences (k n : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      let prev := sequences k' n in
      concat (map (fun s =>
        map (fun i => i :: s) (seq 0 n)
      ) prev)
  end.

Fixpoint pick (H : lowprog) (i : nat) : low_term :=
  nth i H (0%R, fun _ => paulii).

(* ================= SELECT operator ================= *)

Definition select (H : lowprog) (seq : list nat) : lowprog :=
  map (fun i => pick H i) seq.

(* ================= ancilla qubits ================= *)

Definition ancilla_qubits (j : nat) : nat :=
  S (Nat.log2 j).

(* ================= PREPARE ================= *)

Definition prepare (coeffs : list C) : list C :=
  coeffs.

(* ================= UNPREPARE ================= *)

Definition unprepare (v : list C) : list C :=
  v.

(* ================= LCU-Taylor single segment ================= *)

Definition lcu_taylor_segment (H : lowprog) (t : R) (K : nat) : lowprog :=
  concat (
    map (fun k =>
      map (fun seq =>
        scale_term (taylor_coeff k t)
          (fold_left (fun acc i =>
            let h := pick H i in
            (fst acc * fst h, pauli_string_mul (snd acc) (snd h))
          ) seq (1%R, fun _ => paulii))
      ) (sequences k (length H))
    ) (seq 0 K)
  ).

(* ================= Trotter splitting ================= *)

Definition delta_t := (t / INR r)%R.

Fixpoint trotter (H : lowprog) (r : nat) : lowprog :=
  match r with
  | 0 => []
  | S r' =>
      lcu_taylor_segment H delta_t K ++ trotter H r'
  end.

(* ================= FULL LCU-TAYLOR EVOLUTION ================= *)

Definition lcu_taylor (H : lowprog) : lowprog :=
  let grouped := group_commuting H in
  concat (map (fun g => trotter g r) grouped).

(* ================= OUTPUT ================= *)

Definition output := lcu_taylor H.