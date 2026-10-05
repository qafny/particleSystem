From Coq Require Import List Reals Psatz.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.

Local Open Scope R_scope.


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

Fixpoint qdrift_sum_w (input : norm_prog) (n : nat) : R :=
  match n, input with
  | 0, _ => R0
  | _, [] => R0
  | S n', (amp, _) :: rem =>
      (Rabs amp + qdrift_sum_w rem n')%R
  end.

Definition qdrift_step (err t : R) (input : norm_prog) : nat := 
  let lambda := qdrift_sum_w input (length input) in
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

Fixpoint sample_acc (lp : lowprog) (N : nat) (totw : R) (acc : lowprog) : lowprog :=
  match N with
  | O => rev acc
  | S n' =>
    match sample_once lp (random_float totw) with
    | [] => sample_acc lp n' totw acc
    | x :: _ => sample_acc lp n' totw (x :: acc)
    end
  end.

Definition sample (lp : lowprog) (N : nat) (totw : R) : lowprog :=
  sample_acc lp N totw [].

Fixpoint qdrift_sample_once
  (lp : norm_prog) (num : R) : norm_prog :=
  match lp with
  | [] => []
  | (w, h) :: app =>
      if Rltb num (Rabs w)
      then
        if Rltb w R0
        then [(Rminus R0 R1, h)]
        else [(R1, h)]
      else qdrift_sample_once app (Rminus num (Rabs w))
  end.


Fixpoint qdrift_sample_acc
  (lp : norm_prog) (N : nat) (totw : R)
  (acc : norm_prog) : norm_prog :=
  match N with
  | O => rev acc
  | S n' =>
      match qdrift_sample_once lp (random_float totw) with
      | [] => qdrift_sample_acc lp n' totw acc
      | x :: _ => qdrift_sample_acc lp n' totw (x :: acc)
      end
  end.


Definition qdrift_sample
  (lp : norm_prog) (N : nat) (totw : R) : norm_prog :=
  qdrift_sample_acc lp N totw [].

Definition trotter_qdrift
  (err t : R) (lp : norm_prog) : norm_prog :=
  let N := qdrift_step err t lp in
  let totw := qdrift_sum_w lp (length lp) in
  mult_r_normprog
    (totw / INR N)
    (qdrift_sample lp N totw).

(* ================================================================ *)
(* QDrift probability lemmas                                        *)
(* ================================================================ *)

Lemma qdrift_sum_w_cons :
  forall (amp : R) (f : nat -> paulimat) rem,
    qdrift_sum_w ((amp, f) :: rem)
                  (length ((amp, f) :: rem))
    =
    Rabs amp + qdrift_sum_w rem (length rem).
Proof.
  intros amp f rem.
  simpl.
  reflexivity.
Qed.

Fixpoint qdrift_prob_sum
  (lam : R) (hlist : norm_prog) : R :=
  match hlist with
  | [] => 0
  | (amp, _) :: rem =>
      Rabs amp / lam + qdrift_prob_sum lam rem
  end.

Lemma qdrift_prob_sum_eq :
  forall lam hlist,
    lam <> 0 ->
    qdrift_prob_sum lam hlist
    =
    qdrift_sum_w hlist (length hlist) / lam.
Proof.
  intros lam hlist Hlam.
  induction hlist as [| [amp f] rem IH].
  - change (0 = 0 / lam).
    unfold Rdiv.
    ring.

  - cbn [qdrift_prob_sum].
    rewrite IH.

    change
      (Rabs amp / lam +
       qdrift_sum_w rem (length rem) / lam =
       (Rabs amp + qdrift_sum_w rem (length rem)) / lam).

    field.
    exact Hlam.
Qed.

Lemma qdrift_prob_sum_one :
  forall lam hlist,
    lam > 0 ->
    lam = qdrift_sum_w hlist (length hlist) ->
    qdrift_prob_sum lam hlist = 1.
Proof.
  intros lam hlist Hlam Hsum.
  rewrite qdrift_prob_sum_eq.
  - rewrite <- Hsum.
    field.
    lra.
  - lra.
Qed.

Definition qdrift_sign (amp : R) : R :=
  if Rltb amp R0 then (-1)%R else 1.



