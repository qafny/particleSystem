(* Define the trotterization step, Lie-Trotter fomular, qdrift *)
Require Import QuantumLib.Matrix.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueTrotter.

(* exp(-i t H) *)
Parameter expH : R -> lowprog -> lowprog.

(* This is the input for sythesization *)
Definition ugate := (R * lowprog) %type.
Parameter exp_ugate : R -> lowprog -> ugate. (* exp(-i r H) *)
(* Norm of H matrix *)
Parameter norm : lowprog -> R.


(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator_tt (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-myC1)%C [ten_app_ten h2 h1]).

Definition commutator_st (h1 : lowprog) (h2 : lowprog_ten) : lowprog :=
  let l1 := plus_app_ten h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (ten_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition commutator_ts (h1 : lowprog_ten) (h2 : lowprog) : lowprog :=
  let l1 := ten_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_ten h2 h1) in
  plus_plus_plus l1 l2.

(* Drop first n elements of a list. *)
Fixpoint drop_nth {A : Set} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | S n', _ :: xs => drop_nth n' xs
  | _, [] => []
  end.

(* Eval compute in drop_nth 2 [10; 20; 30; 40]. 
Returns [30; 40] *)

Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with 
  | [] => []
  | h :: rem => commutator_st rem h
  end.

(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
Fixpoint trotter_error_bound_helper (idx : nat) (hlist : lowprog) : R :=
  match idx with
  | 0 => 0
  | S k => let comm_sum := comm_sums idx hlist in
      Rplus (norm comm_sum) (trotter_error_bound_helper k hlist)
  end.

Definition trotter_error_bound (t : R) (hlist : lowprog) : R :=
  let gamma := length hlist in
  (t*t/2) * (trotter_error_bound_helper gamma hlist). 


(**** Approximate central value using 1st-order std Trotter ****)
(* Approx = exp(-itH_1)exp(-itH_2) ... *)
Fixpoint e_split (t : R) (hlist : lowprog) : lowprog :=
    match hlist with [] => []
    | h :: ht => plus_app_plus (expH t [h]) (e_split t ht)
    end.

(* Theorem First_order_trotter: .
Proof.
  
Qed. *)



(* Tight error bound for the second-order Suzuki formula. *)
Definition commutator_ss (h1 : lowprog) (h2 : lowprog) : lowprog :=
  let l1 := plus_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition suzuki_comm_sum_helper (hlist : lowprog) : (lowprog * lowprog) :=
  match hlist with 
  | [] => ([], [])
  | x :: rem => 
    let t1 := commutator_ss rem (commutator_st rem x) in
    let t2 := commutator_ts x (commutator_ts x rem) in (t1, t2)
    end.

Fixpoint suzuki_error_bound (t: R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | x :: ax => let (term1, term2) := suzuki_comm_sum_helper hlist in
      Rplus (Rplus (Rdiv ((norm term1) * (pow t 3)) 12)
                   (Rdiv ((norm term2) * (pow t 3)) 24))
            (suzuki_error_bound t ax)
  end.

Definition e_split_suzuki (t : R) (hlist : lowprog) : lowprog := 
  let term1 : lowprog := e_split t (rev hlist) in
  let term2 : lowprog := e_split t hlist in
  plus_app_plus term1 term2.



(* Trotterization: Tight error bound for the first-order Lie-Trotter formula *)
(* A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem lie_trotter_error_bound :
  forall (t : R) (hlist : lowprog),
  let approx := e_split t hlist in
  let gold := expH t hlist in
  Rle (norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)))
    (trotter_error_bound t hlist).

Proof.
  intros t hlist approx gold.
  

Admitted.


Theorem suzuki_second_order_error_bound :
  forall (t : R) (hlist : lowprog),
  let approx := e_split_suzuki t hlist in
  let gold := expH t hlist in
  Rle (norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)))
      (suzuki_error_bound t hlist).
Proof. Admitted.
 
