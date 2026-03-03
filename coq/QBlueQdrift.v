From Coq Require Import List.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* Decide N using epsilon based on QDrift error boundary. *)
(* err = 2 * lamda^2 * t^2 / N *)
(* TODO: need prove z = fst z *)
(* sum up the first n weights in sum_i wi Hi *)
Fixpoint sum_w (input : lowprog) (n : nat) : R :=
  match n, input with
  | 0, _ => R0
  | _, [] => R0
  | S n', (z, _) :: rem => (Rabs (fst z) + (sum_w rem n'))%R
  end.

Definition qdrift_step (err t : R) (input : lowprog) : nat := 
  let lambda := sum_w input (length input) in
  let n1 := ceilR_N (R2 * lambda * lambda * t * t / err) in 
	ceilR_N ((INR n1) * (exp (R2 * t * lambda / (INR n1)))).

Fixpoint sample_once (lp : lowprog) (num : R) : lowprog :=
  match lp with 
  | [] => []
  | (w, h) :: app => if Rltb num (Rabs (fst w)) 
    then if Rltb (fst w) R0 
      then [(RtoC (Rminus R0 R1), h)] 
      else [(C1, h)]
    else sample_once app (Rminus num (Rabs (fst w)))
  end.

Fixpoint sample (lp : lowprog) (N : nat) (totw : R) : lowprog :=
  match N with
  | O => []
  | S n' => (sample_once lp (random_float totw)) ++ (sample lp n' totw)
  end.

Definition trotter_qdrift (err t : R) (lp : lowprog) : lowprog :=
  let N := qdrift_step err t lp in
  let totw := sum_w lp (length lp) in
  mult_r_hplus (totw * t / (INR N)) (sample lp N totw).
