(*************************************************************************)
(* QBlueTTS_v4.v                                                         *)
(* Truncated Taylor series LCU (Berry, Childs, Cleve, Kothari, Somma   *)
(* 2015) with oblivious amplitude amplification per segment.            *)
(* Built from the shared LCU blocks in QBlueQuantumWalk.v.               *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ratan.
Require Import Coq.Arith.PeanoNat.
Require Import QuantumLib.Complex.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueQuantumWalk.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Truncated Taylor series (Berry, Childs, Cleve, Kothari, Somma 2015)  *)

Fixpoint fact_R (k : nat) : R := match k with O => 1 | S k' => INR k * fact_R k' end.

Definition exp_tail (x : R) (K : nat) : R :=
  fold_left Rplus (map (fun k => pow x k / fact_R k) (seq (S K) 40)) 0.

Fixpoint taylor_K_aux (fuel K : nat) (x delta : R) : nat :=
  match fuel with
  | O => K
  | S f => if Rle_dec (exp_tail x K) delta then K else taylor_K_aux f (S K) x delta
  end.

(* smallest K >= 1 with sum_{k > K} x^k / k! <= delta *)
Definition taylor_K (x delta : R) : nat := Nat.max 1 (taylor_K_aux 60 0 x delta).

Record taylor_layout := { tl_u : list nat; tl_idx : list (list nat); tl_pad : nat; tl_work : list nat }.

Definition taylor_alloc (nbit a K : nat) : taylor_layout :=
  let u := qrange nbit K in
  let idx := map (fun i => qrange (nbit + K + i * a) a) (seq 0 K) in
  let p := (nbit + K + K * a)%nat in
  {| tl_u := u; tl_idx := idx; tl_pad := p; tl_work := qrange (S p) (K + K * a) |}.

Definition taylor_nqubits (nbit a K : nat) : nat := (nbit + 2 * (K + K * a) + 1)%nat.

(* unary register: u_i = 1 iff k > i, amplitudes al_k *)
Definition unary_prep (al : list R) (u : list nat) : gl :=
  let r i := sqrt (fold_left Rplus (map (fun v => v * v) (skipn i al)) 0) in
  match u with
  | [] => []
  | u0 :: _ =>
      Ry (ry_angle_cos (nth 0 al 0)) u0 ::
      flat_map (fun i =>
        let ri := r i in
        let c := if Rlt_dec 0 ri then rmin1 (nth i al 0 / ri) else 1 in
        cry (ry_angle_cos c) (nth (i - 1) u O) (nth i u O)) (seq 1 (length u - 1))
  end.

(* <0|A|0> = (1/2) sum_{k <= K} (-i tau H)^k / k!, x = lambda tau *)
Definition taylor_segment (nbit : nat) (lp : lowprog) (x : R) (K : nat) (L : taylor_layout) : gl :=
  let beta := map (fun k => pow x k / fact_R k) (seq 0 (S K)) in
  let B := fold_left Rplus beta 0 in
  let al := map (fun b => sqrt (b / B)) beta in
  let up := unary_prep al (tl_u L) in
  [Ry (pad_angle B) (tl_pad L)] ++ up ++ map (fun q => U1 (- (PI / 2)) q) (tl_u L)
  ++ flat_map (fun reg => prep lp reg) (tl_idx L)
  ++ flat_map (fun i => select nbit lp (nth i (tl_idx L) []) (tl_work L) [nth i (tl_u L) O])
             (seq 0 K)
  ++ flat_map (fun reg => inv_gl (prep lp reg)) (tl_idx L)
  ++ inv_gl up.

(* the segment without its K controlled SELECTs (resource accounting) *)
Definition taylor_segment_rest (nbit : nat) (lp : lowprog) (x : R) (K : nat) (L : taylor_layout) : gl :=
  let beta := map (fun k => pow x k / fact_R k) (seq 0 (S K)) in
  let B := fold_left Rplus beta 0 in
  let al := map (fun b => sqrt (b / B)) beta in
  let up := unary_prep al (tl_u L) in
  [Ry (pad_angle B) (tl_pad L)] ++ up ++ map (fun q => U1 (- (PI / 2)) q) (tl_u L)
  ++ flat_map (fun reg => prep lp reg) (tl_idx L)
  ++ flat_map (fun reg => inv_gl (prep lp reg)) (tl_idx L)
  ++ inv_gl up.

Definition taylor_segments (lp : lowprog) (t : R) : nat :=
  Nat.max 1 (ceilR_N (lcu_lambda lp * t / ln 2)).

(* e^{-iHt} up to the global phase (-1)^r: r OAA'd segments *)
Definition taylor_circuit (err t : R) (nbit : nat) (lp0 : lowprog) : gl :=
  let lp := lcu_terms lp0 in
  let r := taylor_segments lp t in
  let x := lcu_lambda lp * t / INR r in
  let K := taylor_K x (err / (4 * INR r)) in
  let L := taylor_alloc nbit (idx_width lp) K in
  let A := taylor_segment nbit lp x K L in
  repeat_gl r (oaa A (tl_u L ++ concat (tl_idx L) ++ [tl_pad L]) (tl_work L)).

(* ---------------------------------------------------------------------- *)
(* Resource accounting (see QBlueQuantumWalk.v)                            *)

Definition taylor_pieces (err t : R) (nbit : nat) (lp0 : lowprog) : lcu_report :=
  let lp := lcu_terms lp0 in
  let r := taylor_segments lp t in
  let x := lcu_lambda lp * t / INR r in
  let K := taylor_K x (err / (4 * INR r)) in
  let a := idx_width lp in
  let L := taylor_alloc nbit a K in
  let R := refl0 (tl_u L ++ concat (tl_idx L) ++ [tl_pad L]) (tl_work L) [] in
  (* the K controlled SELECTs are the same gates on relabelled registers, so one
     stands for all of them; it is counted on a canonical layout (control nbit,
     index register, then work) that does not move with K, so its cached counts
     are reused across error bounds and times *)
  let sel := select nbit lp (qrange (S nbit) a) (qrange (S nbit + a) a) [nbit] in
  (taylor_nqubits nbit a K, r, K,
   [(3 * r, taylor_segment_rest nbit lp x K L); (3 * r * K, sel); (2 * r, R)]%nat).

