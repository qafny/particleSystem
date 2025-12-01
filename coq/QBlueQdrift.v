Require Import QuantumLib.Matrix.

(* Qdrift trotterization *)
(* Definition of L: a matrix. It relies on Hamiltonian H. It operates on the state |phi><phi| *)
(* L(rho) = i(H rho - rho H). This matrix takes rho and do commutation i[H, rho] *)
Variable nd : nat. 
Definition TransL := Matrix nd nd.
Parameter L_h : list R. (* hj *)
Parameter L_Lori : list TransL. (* Lj *)           
Parameter L_sampledID : list nat. (* Sampled IDs. if L1 = [1,3,3,2], chose L[3] twice *)
(* Diamond norm, the sum of singular values in the space with ancilla qubits considered. *)
Parameter norm_diamond : TransL -> R.
(* Transform L to exp(tL). *)
Parameter expH1 : R -> TransL -> TransL.

(* Require each Lj to have a strength hj *)
Axiom length_match :
  length L_sampledID = length L_h.

Definition lambda : R := fold_right Rplus 0%R L_h.

(* Theorem for qdrift. *)
(* calculate L = sum_j (hj Lj) *)
Fixpoint sum_L (prob : list R) (ll : list TransL) : TransL :=
  match prob, ll with 
  | [], _ => Zero
  | _, [] => Zero
  | p :: pl, m :: ml => Mplus (scale p m) (sum_L pl ll) 
  end.

Definition tau (t : R) : R := lambda * t / (INR (length L_sampledID)).

(* Generate the sampled list based on the sampled ID idl and the original list vl. *)
Fixpoint sum_sampled_exp (t : R) (idl : list nat) : TransL :=
  match idl with
  | [] => Zero
  | id :: ax =>
    match (nth_error L_Lori id, nth_error L_h id) with
    | (None, _) => Zero
    | (_, None) => Zero
    | (Some Lj, Some hj) => Mplus (scale (hj / lambda) (expH1 (tau t) Lj)) (sum_sampled_exp t ax)
    end
  end.

Definition qdrift_error (t : R) : R :=   
  let N : R := INR (length L_sampledID) in
  let gold := expH1 (t / N) (sum_L L_h L_Lori) in
  let approx := sum_sampled_exp t L_sampledID in
  0.5 * (norm_diamond (Mplus gold (-1 .* approx))).


