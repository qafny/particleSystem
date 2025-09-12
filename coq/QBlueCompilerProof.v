Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueSemanticsProof.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueCompiler.
Local Open Scope R_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

From SQIR Require Import SQIR. 

(* Particle Transformation *)

Lemma in_state_map_iff :
  forall (l:psi) (τ:iota) (e:C * basisKet),
    In e (state_map l τ) <->
    exists x, In x l /\ state_map_basis x τ = e.
Proof.
  intros l τ e. unfold state_map. rewrite in_map_iff. firstorder. 
Qed.

Lemma WFKet_state_map_basis_bin :
  forall (sty : iota) (s : C * basisKet),
    WFKet sty (snd s) ->
    WFKet (state_type_bin sty) (snd (state_map_basis s (state_type_bin sty))).
Proof.
  intros sty s IH.
  destruct sty as [| a sty'].
  - simpl in *. unfold state_map_basis. simpl in *.  
Admitted.


(* Sub lemma for proving particle_transoform_correctness.
  Well-form state is kept when transforming from high-level to low-level *)
Lemma WFState_state_map_bin: forall sty s, WFState sty s ->
  WFState (state_type_bin sty) (state_map s (state_type_bin sty)).
Proof.
  intros sty s Hwf e Hin.
  apply in_state_map_iff in Hin.
  destruct Hin as [x [HxIn Heq]].
  subst e.  
  apply WFKet_state_map_basis_bin.
  apply Hwf. easy.
Qed. 
  

(* Theorem for particle transformation from low-level to high-level *)
Theorem particle_transoform_correctness: forall n st_type e op_type s, 
  typing st_type e op_type -> WFState st_type s -> exists s1,
  let H' := bexp_to_lowprog e st_type in
  let s' := state_map s st_type in
  let st_type' := state_type_bin st_type in
  let s1' := state_map s1 st_type' in
  blue_sem n st_type e s s1 /\ WFState st_type' s1' /\ blue_sem_low H' s' s1'.
  intros n st_type e op_type sin Hty Hwf.
  Proof.
    destruct (type_soundness st_type e op_type n sin Hty Hwf)
    as [s1 [Hsem HWFr]].

    exists s1.

    repeat split.

    - exact Hsem.
    
    - (* WFState (state_type_bin st_type) (state_map s1 (state_type_bin st_type)) *)
    (* Any lemma that says mapping/bin-typing preserves WF works here *)
    apply WFState_state_map_bin; exact HWFr.

    
    - admit. 
      (* apply bexp_to_lowprog_sound; exact Hsem. *)

  
Admitted. 




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



(*********** Qdrift ***************)
Theorem qdrift_error_boundary : 
  forall (t : R),
  let N : R := INR (length L_sampledID) in
  let boundary := 4 * lambda^2 * t^2 / N^2 in 
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



