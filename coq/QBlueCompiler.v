(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Local Open Scope R_scope.
Require Import QBlue.QBlueSyntax.

Require Import List.
Import ListNotations.



(* Commutator: [A, B] = AB - BA *)
Definition commutator (h1 h2 : lowprog) : lowprog :=
  plus_plus_plus (plus_app_plus h1 h2) (mult_ampli_hplus (-C1)%C (plus_app_plus h2 h1)).

(* Norm of H matrix *)
Parameter norm : lowprog -> R.
(* exp(-iHt) *)
Parameter expH : R -> lowprog -> lowprog.


(* Drop first n elements. *)
Fixpoint drop_nth {A : Set} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | S n', _ :: xs => drop_nth n' xs
  | _, [] => []
  end.

(* Eval compute in drop_nth 2 [10; 20; 30; 40]. 
Returns [30; 40] *)

(* sum_{γ2=γ1+1}^Γ [H_{γ2}, H_{γ1}] *)
Definition comm_sums (gamma1 : nat) (hlist : list lowprog) : lowprog :=
    let subl := drop_nth gamma1 hlist in
    let h1 := hd [] subl in
    let htail := tl subl in
    let fix helper (ll : list lowprog) : lowprog :=
        match ll with [] => []
        | h2 :: rem => plus_plus_plus (commutator h2 h1) (helper rem)
        end
    in
    helper htail.


(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
Definition trotter_error_bound (t : R) (hlist : list lowprog) : R :=
    let gamma := length hlist in
    let fix helper (idx : nat) : R :=
        (match idx with
        | 0 => 0
        | S k => let comm_sum := comm_sums idx hlist in
            Rplus (norm comm_sum) (helper k)
    end) in
    (t*t/2) * helper gamma.


Fixpoint e_split (t : R) (hlist : list lowprog) : lowprog :=
    match hlist with [] => []
    | h :: ht => plus_app_plus (expH (-t) h) (e_split t ht)
    end.

Fixpoint sum_lowprog (l : list lowprog) : lowprog :=
    match l with
    | [] => []
    | x :: xs => plus_plus_plus x (sum_lowprog xs)
    end.

(* theorem: Tight error bound for the  rst-order Lie-Trotter formula *)
Theorem lie_trotter_error_bound :
  forall (t : R) (hlist : list lowprog),
  let approx := e_split t hlist in
  let gold := expH (-t) (sum_lowprog hlist) in
  norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)) <=
    trotter_error_bound t hlist.

Proof. Admitted.