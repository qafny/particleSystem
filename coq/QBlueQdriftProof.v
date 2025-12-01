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

(* Exponential expansion of e^{tau L} = 1 + tau L + (tau L)^2/2! + ... + (tau L)^k/k! *)
Fixpoint exp_expansion_m {n} (tau : R) (L : Matrix n n) (k : nat) : Matrix n n :=
  match k with
  | 0 => I n
  | S k' =>
      let term := scale ((tau ^ k) / (INR (fact k))) (Mmult_n k L) in
      Mplus (exp_expansion_m tau L k') term
  end.

(* https://arxiv.org/pdf/1711.10980, Lemma F.2 *)
(* used in Appendix B11, "A random compiler for fast Hamiltonian simulation" *)
(* 4. sum_k^∞ x^k/k! <= x^(k+1)/(k+1)! e^x *)
Lemma exp_tail_bound : 
  forall {x : R} {n : nat}, exp_expansion x n - (1+x) <= x^2/2 * (exp x).
Proof. Admitted.

(* 5. dianorm >= 0 *)
Axiom dianorm_nonneg :
  forall (A : TransL), 0 <= norm_diamond A.

(* 6. dianorm inequality *)
(* |A + B| < |A| + |B|, |.| is norm_diamond   *)
Axiom dianorm_triangle :
  forall {n m} (A B : Matrix n m),
    norm_diamond  (Mplus A B) <= (norm_diamond A) + (norm_diamond B).

(* |AB| < |A| * |B| *)
Axiom dianorm_submultiplicative :
  forall {n m p} (A : Matrix n m) (B : Matrix m p),
    norm_diamond (Mmult A B) <= (norm_diamond A) * (norm_diamond B).

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



