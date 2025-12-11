(* Define the trotterization step, Lie-Trotter fomular, Qdrift *)
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.


(* Currently we decide N using epsilon based on QDrift error boundary. *)
(* err = 2 * lamda^2 * t^2 / N *)
(* TODO: need prove z = fst z *)
Fixpoint cal_lambda (input : lowprog) : R :=
  match input with
  | [] => R0
  | (z, _, _) :: rem => Rplus (fst z) (cal_lambda rem)
  end.

Definition trotter_step (err t : R) (input : lowprog) : nat := 
  let lambda := cal_lambda input in
  Rceil_nat (R2 * lambda * lambda * t * t / err).


(* split input into small steps by standard trotterization *)
Definition trotter_aten (N : nat) (aten : lowprog_ten) : lowprog :=
  match aten with (z, n, f) =>
  let z' : C := (Rdiv (fst z) (INR N), Rdiv (snd z) (INR N)) in
  let fix helper n1 : lowprog := match n1 with 
  | 0 => []
  | S n1' => (z', n, f) :: (helper n1') 
  end in helper N
  end. 


(* Low-level Hamiltonian after being trottered into more steps. *)
Fixpoint trotter (err t: R) (input : lowprog) : lowprog :=
  let N := trotter_step err t input in
  match input with 
  | [] => []
  | x :: ax => plus_plus_plus (trotter_aten N x) (trotter err t ax)
  end.


