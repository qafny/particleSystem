(* Define the trotterization step, Lie-Trotter fomular, Qdrift.
   Operates on norm_prog (real amplitude) rather than lowprog (complex
   amplitude) -- at the Pauli-string level every Hamiltonian term's
   coefficient is real (paper's Definition 3.1), so this is the natural
   representation and avoids unnecessary complex-number bookkeeping. *)
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* Step counts come from the commutator error bounds proved in QBlueTrotterProof.v
   (trotter_first_order_error, trotter_second_order_error): N steps of the product
   formula err at most N * bound(t/N). For Pauli terms h_j P_j these bounds have
   cheap upper bounds, because two Pauli strings either commute or satisfy
   ||[P, Q]|| = 2 and ||P|| = 1. Each Pauli string is first turned into a list of
   its n single-qubit factors. *)
Definition pauli_terms (n : nat) (input : norm_prog) : list (R * list paulimat) :=
  map (fun x => (Rabs (fst x), map (snd x) (seq 0 n))) input.

(* number of sites where both strings are non-identity and differ;
   the strings anticommute exactly when this is odd *)
Fixpoint anti_count (a b : list paulimat) : nat :=
  match a, b with
  | x :: xs, y :: ys =>
      (if andb (andb (negb (is_i x)) (negb (is_i y))) (negb (paulimat_eqb x y))
       then 1 else 0) + anti_count xs ys
  | _, _ => 0
  end.

(* D_k = sum over later terms j of ||[c_j P_j, c_k P_k]|| <= 2 |c_j c_k| for anticommuting pairs *)
Fixpoint comm_weight (c : R) (p : list paulimat) (rest : list (R * list paulimat)) : R :=
  match rest with
  | [] => R0
  | (c', p') :: r =>
      ((if Nat.odd (anti_count p p') then R2 * c * c' else R0) + comm_weight c p r)%R
  end.

Fixpoint weight_sum (l : list (R * list paulimat)) : R :=
  match l with
  | [] => R0
  | (c, _) :: r => (c + weight_sum r)%R
  end.

(* first order: sum_k ||[sum_{j>k} H_j, H_k]|| <= C1 *)
Fixpoint comm_sum1 (l : list (R * list paulimat)) : R :=
  match l with
  | [] => R0
  | (c, p) :: rest => (comm_weight c p rest + comm_sum1 rest)%R
  end.

(* second order, per suffix (X = c_k P_k, R = rest):
   ||[R,[R,X]]|| / 12 + ||[X,[X,R]]|| / 24 <= D_k (lambda_rest / 6 + c_k / 12) *)
Fixpoint comm_sum2 (l : list (R * list paulimat)) : R :=
  match l with
  | [] => R0
  | (c, p) :: rest =>
      (comm_weight c p rest * (weight_sum rest / 6 + c / 12) + comm_sum2 rest)%R
  end.

(* N steps of first-order Trotter err at most t^2 C1 / (2N) *)
Definition trotter_step (err t : R) (n : nat) (input : norm_prog) : nat :=
  let C1 := comm_sum1 (pauli_terms n input) in
  Nat.max 1 (ceilR_N (t * t * C1 / (R2 * err))).


(* split input into small steps by standard trotterization
exp(-it (H1 + H2 + H3)) => exp(-it/N (H1 + H2 + H3))
*)
Definition trotter_astep (N : R) (ap : norm_prog) : norm_prog :=
  mult_r_normprog (R1 / N) ap.


Fixpoint trotter_nstep_acc (N : nat) (ap : norm_prog) (acc : norm_prog) : norm_prog :=
  match N with
  | 0 => rev acc
  | S n => trotter_nstep_acc n ap (rev_append ap acc)
  end.

Definition trotter_nstep (N : nat) (ap : norm_prog) : norm_prog :=
  trotter_nstep_acc N ap [].

(* Low-level Hamiltonian after being trottered into more steps. *)
Definition trotter (err t: R) (n : nat) (input : norm_prog) : norm_prog :=
  let N := trotter_step err t n input in
  let astep := trotter_astep (INR N) input in
  trotter_nstep N astep.

(* 2nd order trotterization: N steps err at most |t|^3 C2 / N^2, with C2 taken on
   (rev input), the list the second-order bound is proved for *)
Definition trotter_step_2nd_order (err t : R) (n : nat) (input : norm_prog) : nat :=
  let C2 := comm_sum2 (pauli_terms n (rev input)) in
  Nat.max 1 (ceilR_N (sqrt (Rabs t * Rabs t * Rabs t * C2 / err))).

Definition trotter_2nd_order (err t: R) (n : nat) (input : norm_prog) : norm_prog :=
  let N := trotter_step_2nd_order err t n input in
  let astep1 := trotter_astep ((INR N) * R2) (rev input) in
  let astep2 := trotter_astep ((INR N) * R2) input in
  trotter_nstep N (astep1 ++ astep2).
