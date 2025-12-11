(* Define the trotterization step, Lie-Trotter fomular, qdrift *)
Require Import QuantumLib.Matrix.

Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueTrotter.

(* TODO: How to instantialize norm? *)

(* Norm of H matrix *) 
Parameter norm : forall n : nat, Square n -> R.

(* exp(-i t H) *)
Parameter expH : forall n : nat, R -> Square n -> Square n.


(**** Approximate central value using 1st-order std Trotter ****)
(* Approx = exp(-itH_1)exp(-itH_2) ... *)
Fixpoint approx_trotter_exp (t : R) (hlist : lowprog) (n : nat) : Square (2^n) :=
  match hlist with 
  | [] => I (2^n)
  | (amp, n, f) :: ht => Mmult (expH (2^n) t (lowprogten2mat amp n f)) (approx_trotter_exp t ht n)
    end.

(* Gold error: || e^{-i H t} - PI_i (e^{-i Hi t}) ||
n: # of paulis in one pauli string *)
Definition cal_1st_trotter_error (t : R) (lp : lowprog) : R :=
  match lp with 
  | [] => 0
  | (_, n, _) :: rem =>
    let exp_mat_gold := expH (2^n) t (lowprog2mat lp n) in 
    let exp_mat_approx := approx_trotter_exp t lp n in
    norm (2^n) (Mplus exp_mat_approx (scale (-R1) exp_mat_gold))
  end.

(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator_tt (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-myC1) [ten_app_ten h2 h1]).

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

(* [sum_{i=γ1+1, n} H_i, H_γ1], γ1 starts from 0 *)
Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with 
  | [] => []
  | h :: rem => commutator_st rem h
  end.

(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
(* idx: γ1, start from 0; n: # of paulis in one string; hlist: trottered input lowprog *) 
Fixpoint trotter_error_bound_helper (idx n : nat) (hlist : lowprog) : R :=
  match idx with
  | 0 => 0
  | S k => let comm_sum := lowprog2mat (comm_sums idx hlist) n in
      Rplus (norm (2 ^ n) comm_sum) (trotter_error_bound_helper k n hlist)
  end.

(* 1st-order error: t^2/2 * ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] *)
Definition cal_1st_trotter_error_bound (t : R) (hlist : lowprog) : R :=
  let gamma := length hlist in
  match hlist with
  | [] => 0
  | (_, n, _) :: _ => (t*t/2) * (trotter_error_bound_helper gamma n hlist)
  end. 


(* Trotterization: error bound for the first-order Lie-Trotter formula *)
(* A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem first_trotter_error_bound: forall (lp: lowprog) (t err err_bound : R),
  err = cal_1st_trotter_error t lp
  -> err_bound = cal_1st_trotter_error_bound t lp 
  -> err <= err_bound.
Proof.
Admitted.


(**** Approximate central value using 2nd-order std Trotter ****)
(* Approx = exp(-it/2 H_1)exp(-it/2 H_2) ... exp(-it/2 H_n)exp(-it/2 H_{n-1}) ... *)
Definition approx_trotter_exp_2nd (t : R) (hlist : lowprog) (n : nat) : Square (2^n) := 
  let term1 := approx_trotter_exp (t/2) (rev hlist) n in
  let term2 := approx_trotter_exp (t/2) hlist n in
  Mmult term1 term2.

(* Gold error for 2nd-order trotter:
n: # of paulis in one pauli string *)
Definition cal_2nd_trotter_error (t : R) (lp : lowprog) : R :=
  match lp with 
  | [] => 0
  | (_, n, _) :: rem =>
    let exp_mat_gold := expH (2^n) t (lowprog2mat lp n) in 
    let exp_mat_approx := approx_trotter_exp_2nd t lp n in
    norm (2^n) (Mplus exp_mat_approx (scale (-R1) exp_mat_gold))
  end.


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

Fixpoint suzuki_error_bound_helper (n : nat) (t: R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | x :: ax => let (term1, term2) := suzuki_comm_sum_helper hlist in
      let t1 := lowprog2mat term1 n in
      let t2 := lowprog2mat term2 n in
      Rplus (Rplus (Rdiv ((norm (2 ^ n) t1) * (pow t 3)) 12)
                   (Rdiv ((norm (2 ^ n) t2) * (pow t 3)) 24))
            (suzuki_error_bound_helper n t ax)
  end.

(* 2nd-order error *)
Definition cal_2nd_trotter_error_bound (t : R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | (_, n, _) :: _ => suzuki_error_bound_helper n t hlist
  end.


Theorem second_trotter_error_bound: forall (lp: lowprog) (t err err_bound : R),
  err = cal_2nd_trotter_error t lp
  -> err_bound = cal_2nd_trotter_error_bound t lp 
  -> err <= err_bound.
Proof.
Admitted.

 
