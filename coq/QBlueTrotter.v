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
  let L := INR (length input) in
  let n1 := (L * L * t * t / err)%R in
  ceilR_N (n1 * (exp (t * L / n1))). 


(* split input into small steps by standard trotterization 
exp(-it (H1 + H2 + H3)) => exp(-it/N (H1 + H2 + H3)) 
*)
Definition trotter_astep (N : R) (ap : lowprog) : lowprog :=
  map (fun p =>
    let '(z, f) := p in
    let z' : C := (Rdiv (fst z) N, Rdiv (snd z) N) in
    (z', f)) ap.


Fixpoint trotter_nstep_acc (N : nat) (ap : lowprog) (acc : lowprog) : lowprog :=
  match N with
  | 0 => rev acc
  | S n => trotter_nstep_acc n ap (rev_append ap acc)
  end.

Definition trotter_nstep (N : nat) (ap : lowprog) : lowprog :=
  trotter_nstep_acc N ap [].

(* Low-level Hamiltonian after being trottered into more steps. *)
Definition trotter (err t: R) (input : lowprog) : lowprog :=
  let N := trotter_step err t input in
  let astep := trotter_astep (INR N) input in
  trotter_nstep N astep.

(* 2nd order trotterization *)
(* Use "Toward the first quantum simulation with quantum speedup" by Andrew M. Childs etc.
Proposition F.4: err = (2L Lamda t)^3 / 3r^2 * exp(2L Lamda t / r) *)
(* Lamda = largest norm of Hi, it is 1 for pauli tensors *)
(* r = N/L; L: number of terms *)
Definition trotter_step_2nd_order (err t : R) (input : lowprog) : nat := 
  let L := INR (length input) in
  let n1 := sqrt ((pow (R2 * L * Rabs t) 3%nat) / ((R2 + R1) * err)) in
  ceilR_N (n1 * (exp (R2 * t * L / n1))). 

Definition trotter_2nd_order (err t: R) (input : lowprog) : lowprog :=
  let N := trotter_step_2nd_order err t input in
  let astep1 := trotter_astep ((INR N)/R2) (rev input) in
  let astep2 := trotter_astep ((INR N)/R2) input in
  trotter_nstep N (astep1 ++ astep2).

