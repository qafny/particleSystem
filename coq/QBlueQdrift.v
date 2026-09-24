From Coq Require Import List.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


(* Decide N using epsilon based on QDrift error boundary. *)
(* err = 2 * lamda^2 * t^2 / N *)
(* TODO: need prove z = fst z *)
(* sum up the first n weights in sum_i wi Hi *)
Fixpoint sum_w (input : norm_prog) (n : nat) : R :=
  match n, input with
  | 0, _ => R0
  | _, [] => R0
  | S n', (amp, _) :: rem => (Rabs amp + (sum_w rem n'))%R
  end.

Definition qdrift_step (err t : R) (input : norm_prog) : nat := 
  let lambda := sum_w input (length input) in
  let n1 := ceilR_N (R2 * lambda * lambda * t * t / err) in 
	ceilR_N ((INR n1) * (exp (R2 * t * lambda / (INR n1)))).

Fixpoint sample_once (lp : norm_prog) (num : R) : norm_prog :=
  match lp with
  | [] => []
  | (w, h) :: app => if Rltb num (Rabs w)
    then if Rltb w R0
      then [(Rminus R0 R1, h)]
      else [(R1, h)]
    else sample_once app (Rminus num (Rabs w))
  end.


Fixpoint sample_acc (lp : norm_prog) (N : nat) (totw : R) (acc : norm_prog) : norm_prog :=
  match N with
  | O => rev acc
  | S n' =>
    match sample_once lp (random_float totw) with
    | [] => sample_acc lp n' totw acc
    | x :: _ => sample_acc lp n' totw (x :: acc)
    end
  end.

Definition sample (lp : norm_prog) (N : nat) (totw : R) : norm_prog :=
  sample_acc lp N totw [].

Definition trotter_qdrift (err t : R) (lp : norm_prog) : norm_prog :=
  let N := qdrift_step err t lp in
  let totw := sum_w lp (length lp) in
  mult_r_normprog (totw / (INR N)) (sample lp N totw).
