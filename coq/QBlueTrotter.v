(* Define the trotterization step, Lie-Trotter fomular, Qdrift *)
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* Use "Toward the first quantum simulation with quantum speedup" by Andrew M. Childs etc.
Proposition F.3: err = (L Lamda t)^2 / r exp(L Lamda t / r) *)
(* Lamda = largest norm of Hi, it is 1 for pauli tensors *)
(* r = N/L; L: number of terms *)
(* TODO: need prove z = fst z *)
Definition trotter_step (err t : R) (input : lowprog) : nat := 
  let L := length input in
  let n1 := ceilR_N ((INR L) * (INR L) * t * t / err) in
  ceilR_N ((INR n1) * (exp (t * (INR L) / (INR n1)))). 


(* split input into small steps by standard trotterization 
exp(-it (H1 + H2 + H3)) => exp(-it/N (H1 + H2 + H3)) 
*)
Fixpoint trotter_astep (N: nat) (ap : lowprog) : lowprog :=
  match ap with
  | [] => []
  | (z, f) :: aap => 
    let z' : C := (Rdiv (fst z) (INR N), Rdiv (snd z) (INR N)) in 
    (z', f) :: (trotter_astep N aap)
  end.

Fixpoint trotter_nstep (N: nat) (ap : lowprog) : lowprog :=
  match N with 
  | 0 => []
  | S n => ap ++ (trotter_nstep n ap)
  end.

(* Low-level Hamiltonian after being trottered into more steps. *)
Definition trotter (err t: R) (input : lowprog) : lowprog :=
  let N := trotter_step err t input in
  let astep := trotter_astep N input in
  trotter_nstep N astep.


