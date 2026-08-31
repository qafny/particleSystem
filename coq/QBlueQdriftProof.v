Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueCompile.
Require Import QBlue.QBlueParTransJwt.
Local Open Scope R_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

From SQIR Require Import SQIR. 

Local Open Scope matrix_scope.


(* expH: matrix exponential of a Hamiltonian H (dimension nd). *)
(* Truncated Taylor series for exp(- itH) as a matrix: I + (-it)H + (-itH)^2/2! + ... *)
Fixpoint expH (nd : nat) (t : R) (Ham : Square nd) (n : nat) : Square nd :=
  match n with
  | 0 => I nd
  | S n' =>
      let tau := (-Ci * t)%C in
      let term := scale (Cpow tau n / INR (fact n)) (Mmult_n n Ham) in
      Mplus (expH nd t Ham n') term
  end.


(* Liouville commutator on nd×nd density matrices. *)
Definition liouville_comm (nd : nat) (H rho : Square nd) : Square nd :=
  Ci .* (Mminus (Mmult H rho) (Mmult rho H)).

Definition Lfun (nd : nat) (H : Square nd) : Square nd -> Square nd :=
  fun rho => liouville_comm nd H rho.

(* L^n: n-fold application of a superoperator L to a density matrix. *)
Fixpoint Lfun_power_helper (nd : nat) (L : Square nd -> Square nd) (n : nat) (rho : Square nd) : Square nd :=
  match n with
  | 0 => rho
  | S n' => L (Lfun_power_helper nd L n' rho)
  end.

Definition Lfun_power (nd : nat) (L : Square nd -> Square nd) (n : nat) : Square nd -> Square nd :=
  fun rho => Lfun_power_helper nd L n rho.

(* Truncated Taylor series for exp(t L) as a matrix: I + tL + (tL)^2/2! + ... *)
Fixpoint exp_expansion_L (nd : nat) (t : R) (L : Square nd -> Square nd) (n : nat) (rho : Square nd) 
: Square nd :=
  match n with
  | 0 => I nd
  | S n' =>
      let term := scale ((t ^ n) / INR (fact n)) (Lfun_power nd L n rho) in
      Mplus (exp_expansion_L nd t L n' rho) term
  end.


(* expL: matrix exponential of a superoperator L (dimension nd). *)
Definition expL (nd : nat) (t : R) (L : Square nd -> Square nd) (k : nat) : Square nd :=
  exp_expansion_L nd t L k (I nd).


(*********** QDrift channel error (arXiv:1711.10980, Eq. 15-16) ***************)
(* gold = exp^{t L},  L = sum_j h_j L_j
   approx = (sum_j (h_j / lambda) exp^{lambda t / N L_j})^N *)

Fixpoint sum_weighted_gens (nd : nat) (weights : list R) (gens : list (Square nd)) : Square nd :=
  match weights, gens with
  | [], _ => Zero
  | _, [] => Zero
  | w :: wl, g :: gl => Mplus (scale w g) (sum_weighted_gens nd wl gl)
  end.

Fixpoint weighted_exp_channel_sum
  (nd : nat) (exp1 : R -> Square nd -> Square nd)
  (lam t : R) (N : nat) (weights : list R) (gens : list (Square nd)) : Square nd :=
  match weights, gens with
  | [], _ => Zero
  | _, [] => Zero
  | w :: wl, g :: gl =>
    Mplus (scale (w / lam) (exp1 (lam * t / INR N) g))
          (weighted_exp_channel_sum nd exp1 lam t N wl gl)
  end.

Definition expected_qdrift_step
  (nd : nat) (exp1 : R -> Square nd -> Square nd)
  (lam t : R) (N : nat) (weights : list R) (gens : list (Square nd)) : Square nd :=
  weighted_exp_channel_sum nd exp1 lam t N weights gens.

Definition expected_qdrift_channel_N
  (nd : nat) (exp1 : R -> Square nd -> Square nd)
  (lam t : R) (N : nat) (weights : list R) (gens : list (Square nd)) : Square nd :=
  Mmult_n N (expected_qdrift_step nd exp1 lam t N weights gens).

Definition qdrift_gold_channel
  (nd : nat) (exp1 : R -> Square nd -> Square nd) (t : R)
  (weights : list R) (gens : list (Square nd)) : Square nd :=
  exp1 t (sum_weighted_gens nd weights gens).

Definition qdrift_channel_error
  (nd : nat) (dnorm : Square nd -> R) (exp1 : R -> Square nd -> Square nd)
  (lam t : R) (N : nat) (weights : list R) (gens : list (Square nd)) : R :=
  dnorm (Mplus (qdrift_gold_channel nd exp1 t weights gens)
              (Mopp (expected_qdrift_channel_N nd exp1 lam t N weights gens))).

Definition qdrift_channel_error_bound (lam t : R) (N : nat) : R :=
  4 * lam * lam * t * t / (INR N * INR N).

Theorem qdrift_channel_error_bounded :
  forall (nd : nat) (dnorm : Square nd -> R) (exp1 : R -> Square nd -> Square nd)
         (lam t : R) (N : nat) (weights : list R) (gens : list (Square nd)),
    qdrift_channel_error nd dnorm exp1 lam t N weights gens
    <= qdrift_channel_error_bound lam t N.
Proof. Admitted.


(*********** Qdrift setup ***************)
(* L(rho) = i(H rho - rho H) = i[H, rho] on nd×nd matrices.
   TransL = Matrix nd nd for Liouville generators Lj (see L_Lori). *)
Variable nd : nat.
Definition TransL := Matrix nd nd.

Parameter L_h : list R. (* hj: Hamiltonian term weights *)
Parameter L_Lori : list TransL. (* Lj: Liouville generators as nd×nd matrices *)
Parameter L_sampledID : list nat. (* sampled term indices *)

Parameter norm_diamond : TransL -> R.
Parameter expH1 : R -> TransL -> TransL.

Axiom length_match :
  length L_sampledID = length L_h.

Definition lambda : R := fold_right Rplus 0%R L_h.

Definition qdrift_N : nat := length L_sampledID.

Definition qdrift_channel_error_inst (t : R) : R :=
  qdrift_channel_error nd norm_diamond expH1 lambda t qdrift_N L_h L_Lori.

Definition qdrift_channel_error_bound_inst (t : R) : R :=
  qdrift_channel_error_bound lambda t qdrift_N.

Theorem qdrift_channel_error_bounded_inst :
  forall (t : R),
  qdrift_channel_error_inst t <= qdrift_channel_error_bound_inst t.
Proof.
  intros t.
  unfold qdrift_channel_error_inst, qdrift_channel_error_bound_inst.
  apply qdrift_channel_error_bounded.
Qed.


Fixpoint sum_L (prob : list R) (ll : list TransL) : TransL :=
  match prob, ll with
  | [], _ => Zero
  | _, [] => Zero
  | p :: pl, m :: ml => Mplus (scale p m) (sum_L pl ml)
  end.

Definition tau (t : R) : R := lambda * t / (INR (length L_sampledID)).

Fixpoint sum_sampled_exp (t : R) (idl : list nat) : TransL :=
  match idl with
  | [] => Zero
  | id :: ax =>
    match (nth_error L_Lori id, nth_error L_h id) with
    | (None, _) => Zero
    | (_, None) => Zero
    | (Some Lj, Some hj) =>
      Mplus (scale (hj / lambda) (expH1 (tau t) Lj)) (sum_sampled_exp t ax)
    end
  end.

Definition qdrift_error (t : R) : R :=
  let N : R := INR (length L_sampledID) in
  let gold := expH1 (t / N) (sum_L L_h L_Lori) in
  let approx := sum_sampled_exp t L_sampledID in
  0.5 * (norm_diamond (Mplus gold (-1 .* approx))).


(*********** Qdrift ***************)
Theorem qdrift_error_boundary : 
  forall (t : R),
  let N : R := INR (length L_sampledID) in
  let boundary : R := 4 * lambda^2 * t^2 / N^2 in 
  qdrift_error t <= boundary.
Proof.
Admitted.


(* Lemmas for proving qdrift error bound. *)
(* count the # of occur of x in ll. *)
Fixpoint count_occurrences (x : nat) (ll : list nat) : nat :=
  match ll with
  | [] => 0
  | y :: ys =>
      if x =? y then 1 + count_occurrences x ys
      else count_occurrences x ys
  end.

Definition cal_frequency (x : nat) (ll : list nat) : R :=
  let count := count_occurrences x ll in
  let total := length ll in
  if Nat.eqb total 0 then 0
  else (INR count) / (INR total).

(* 1. sampling Lj based on the strength of hj *)
Definition get_prob (id : nat) : R :=
  match (nth_error L_h id) with
    | Some hj => hj / lambda
    | None => 0%R
    end.

Axiom randome_sampling :
  forall (id : nat),
    In id L_sampledID ->
    cal_frequency id L_sampledID = get_prob id.

(* 2. |Lj|_dianorm <= 2, because the largest singular value of Hj is 1. *)
Axiom Lj_norm_bound :
  forall (x : TransL), 
  In x L_Lori -> norm_diamond x <=2.

(* 3. exponential expansion of real number x and matrix *)
(* Exponential expansion of e^{x} = 1 + x + x^2/2! + ... + x^k/k! *)
Fixpoint exp_expansion (x : R) (k : nat) : R :=
  match k with
  | 0 => 1
  | S k' =>
      let term := (x ^ k) / (INR (fact k)) in (exp_expansion x k') + term
  end.

(* exp_expansion_m is defined above with expL. *)

(* https://arxiv.org/pdf/1711.10980, Lemma F.2 *)
(* used in Appendix B11, "A random compiler for fast Hamiltonian simulation" *)
(* 4. sum_k^∞ x^k/k! <= x^(k+1)/(k+1)! e^x *)
Lemma exp_tail_bound :
  forall {x : R} {k : nat}, exp_expansion x k - (1+x) <= x^2/2 * (exp x).
Proof. Admitted.

(* 5. dianorm >= 0 *)
Axiom dianorm_nonneg :
  forall (A : TransL), 0 <= norm_diamond A.

(* 6. dianorm inequality *)
(* |A + B| < |A| + |B|, |.| is norm_diamond   *)
Axiom dianorm_triangle :
  forall (A B : TransL),
    norm_diamond (Mplus A B) <= norm_diamond A + norm_diamond B.

(* |AB| < |A| * |B| *)
Axiom dianorm_submultiplicative :
  forall (A B : TransL),
    norm_diamond (@Mmult nd nd nd A B) <= norm_diamond A * norm_diamond B.

(* |A^k| <= |A|^k for square matrices *)
Lemma dianorm_pow_le :
  forall (A : TransL) (k : nat),
    norm_diamond (Mmult_n k A) <= (norm_diamond A) ^ k.

Proof.
  intros A k.
  induction k as [|k' IH].
  - simpl. (* Assuming norm(I) = 1 *)
    admit. (* Need identity matrix and norm_diamond I = 1 *)
  - simpl. apply Rle_trans with (r2 := norm_diamond A * norm_diamond (Mmult_n k' A)).
    + apply dianorm_submultiplicative.
    + apply Rmult_le_compat_l.
      * apply Rle_trans with (r2 := 0). apply Rle_refl. apply dianorm_nonneg.
      * apply IH.
Admitted.



