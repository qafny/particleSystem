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
	ceilR_N (R2 * lambda * lambda * t * t / err).


(* split input into small steps by standard trotterization 
exp(-it (H1 + H2 + H3)) => exp(-it/N (H1 + H2 + H3)) 
*)
Fixpoint trotter_astep (N: nat) (ap : lowprog) : lowprog :=
  match ap with
  | [] => []
  | (z, n, f) :: aap => 
    let z' : C := (Rdiv (fst z) (INR N), Rdiv (snd z) (INR N)) in 
    (z', n, f) :: (trotter_astep N aap)
  end.

Fixpoint trotter_nstep (N: nat) (ap : lowprog) : lowprog :=
  match N with 
  | 0 => []
  | S n => plus_plus_plus ap (trotter_nstep n ap)
  end.

(* Low-level Hamiltonian after being trottered into more steps. *)
Definition trotter (err t: R) (input : lowprog) : lowprog :=
  let N := trotter_step err t input in
  let astep := trotter_astep N input in
  trotter_nstep N astep.


