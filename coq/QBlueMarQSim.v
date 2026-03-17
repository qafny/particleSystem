From Coq Require Import List.
From Coq Require Import List String ZArith QArith Reals.
Require Import QBlueUtility.
Require Import QBlueSyntax.
From QBlue Require Import QBlueParTransJwt.
From QBlue Require Import QBlueQdrift.


Definition Mat1 := list (list nat).
Definition Mat2 := list (list R).
Definition PauStrType := nat -> paulimat.

(* CNOT matrix, single qubit matrix, probablity matrix *)
Parameter GenPgc: (list R) -> Mat1 -> option Mat1 -> Mat2.

Definition get_trans_func (mat : Mat2) : (nat -> list R) := 
  fun i => nth_default [] mat i.

(* generate the list of the coefficients *)
Definition get_coef (h : lowprog) : list R :=
  map (fun x => fst (fst x)) h.

Definition is_I (p : paulimat) : bool := paulimat_eqb p paulii.

Definition is_XY (p : paulimat) : bool := orb (paulimat_eqb p paulix) (paulimat_eqb p pauliy).


(* calculate the CNOT costs of to Pauli String
n: # of qubits of a pauli string *)
Fixpoint cnot_cost_ops (a b : PauStrType) (n : nat) : nat :=
  match n with 
  | 0 => 0
  | S m => 
    let x := (a m) in 
    let y := (b m) in
    let base := if paulimat_eqb x y then 0%nat else 1%nat in
    let extra := if andb (negb (is_I x)) (negb (is_I y))
      then if paulimat_eqb x y then 0%nat else 1%nat
      else 0%nat in
      base + extra + cnot_cost_ops a b m
  end.

(* calculate the cost of a paulistring with each term of lp:
f: calculate the cost of transition from one pauli string to another, given the total number of qubits. *)
Definition row_costs (f : PauStrType -> PauStrType -> nat -> nat) (row : lowprog_ten) 
  (lp : lowprog) (n : nat) : list nat :=
  map (fun t => f (snd row) (snd t) n) lp.

Fixpoint xy_count (a : PauStrType) (nbit : nat) : nat :=
  match nbit with
  | 0 => 0%nat
  | S m => let x := (a m) in 
    (if is_XY x then 1%nat else 0%nat) + (xy_count a m)
  end.

Fixpoint xy_overlap (a b : PauStrType) (nbit : nat) : nat :=
  match nbit with
  | 0 => 0%nat
  | S m =>
    let x := (a m) in 
    let y := (b m) in
    (if andb (paulimat_eqb x y) (is_XY x) then 1%nat else 0%nat) + (xy_overlap a b m)
  end.

Definition singleQ_cost_ops (a b : PauStrType) (nbit : nat) : nat :=
  (xy_count a nbit) + (xy_count b nbit) - 2 * (xy_overlap a b nbit).

Definition get_CNOT_matrix (lp : lowprog) (nq : nat) : Mat1 :=
  map (fun row => row_costs cnot_cost_ops row lp nq) lp.

Definition get_singleQ_matrix (lp : lowprog) (nbit : nat) : Mat1 :=
  map (fun row => row_costs singleQ_cost_ops row lp nbit) lp.

Definition get_trans_CNOT (lp : lowprog) (nq : nat) : (nat -> list R) := 
  let coef := get_coef lp in
  let cnot := get_CNOT_matrix lp nq in
  let mat := GenPgc coef cnot None in  
  get_trans_func mat.

Definition get_trans_mixed (lp : lowprog) (nq : nat) : (nat -> list R) := 
  let coef : list R := get_coef lp in
  let cnot := get_CNOT_matrix lp nq in
  let sinq := get_singleQ_matrix lp nq in
  let mat := GenPgc coef cnot (Some sinq) in  
  get_trans_func mat.

(* r * m_gc + (1-r) * m_qd, recommend r = 0.6 *)
Definition mix_rows (r : R) (l1 l2 : list R) : list R :=
  map (fun xy => Rplus (Rmult r (fst xy)) (Rmult (R1 - r) (snd xy))) (combine l1 l2).

Definition get_trans_MarQdrift (lp : lowprog) (r : R) (f_gc : nat -> list R) : (nat -> list R) :=
  let coef0 := get_coef lp in
  let totw := sum_w lp (length lp) in
  let coef := map (fun x => Rdiv (Rabs x) totw) coef0 in
  fun x => mix_rows r (f_gc x) coef.


(* Helper function to sample a term from a list of weights. It returns the index of the sampled term. *)
Fixpoint sample_aterm_markov (lp : list R) (num : R) (aux : nat) : nat :=
  match lp with 
  | [] => aux
  | w :: app => if Rltb num (Rabs w) then aux 
    else sample_aterm_markov app (Rminus num (Rabs w)) (S aux)
  end.


(* Based on the given term ID and transition matrix, sample the next term *)
Fixpoint markov_lowprog_acc (prob_init : list R) (lp : lowprog) (termID Nsample : nat)
  (mat : nat -> list R) (acc : lowprog) : lowprog :=
  let rn := random_float 1 in
  match Nsample with
  | 0 => rev acc
  | S n' =>
    let lprob := if Nat.ltb termID 0 then prob_init else mat termID in
    let nid := sample_aterm_markov lprob rn 0 in
    let '(coef, h) := nth_default (C0, fun _ => paulii) lp nid in
    let theT :=
      if Rltb (fst coef) R0
      then (RtoC (Rminus R0 R1), h)
      else (C1, h)
    in markov_lowprog_acc prob_init lp nid n' mat (theT :: acc)
  end.


Definition gen_lowprog_markov (lp : lowprog) (Nsample : nat)  
  (prob_init : list R) (trans_matrix : nat -> list R) : lowprog :=
  markov_lowprog_acc prob_init lp (0 - 1)%nat Nsample trans_matrix []. 


Definition trotter_marqsim (err t : R) (lp : lowprog) (nq : nat) 
(f_mat : nat -> list R) : lowprog :=
  let N := qdrift_step err t lp in
  let prob_init := get_coef lp in
  let trans_matrix := get_trans_CNOT lp nq in 
  let totw := sum_w lp (length lp) in
  mult_r_hplus (totw / (INR N)) (gen_lowprog_markov lp N prob_init trans_matrix).


  

