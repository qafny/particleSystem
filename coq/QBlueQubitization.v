(*************************************************************************)
(* QBlueQubitization.v                                                   *)
(* QSP for Hamiltonian simulation: generalized QSP (Motlagh, Wiebe     *)
(* 2024) on the qubitization walk.                                      *)
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
(* 3. QSP: generalized QSP (Motlagh, Wiebe 2024) on the qubitization walk  *)
(*    e^{-i tau cos theta} = sum_k i^k J_k(tau) z^k for Wm eigenvalue z,  *)
(*    realised as z^{-K} P(z) with P of degree 2K.                         *)

(* ---------------------------------------------------------------------- *)
(* Angle finding by layer stripping (Motlagh, Wiebe 2024, Thm 3)           *)
(*                                                                         *)
(* Polynomials are coefficient lists, index = power of z. GQSP computes    *)
(*   [P(U); Q(U)] = R_d A ... R_1 A v_0,  A = |0><0| (x) U + |1><1| (x) I, *)
(*   R_j = [[u_j^* c_j, u_j^* s_j], [s_j, -c_j]],  v_0 = (p_0', q_0'),     *)
(* for (P, Q) with |P|^2 + |Q|^2 = 1 on the unit circle. Each layer is     *)
(* chosen so that R_j^dag [P; Q] = [z P'; Q'] with P', Q' one degree lower *)
(* (exact when the identity holds exactly; not yet proved in Coq). Only    *)
(* the complementary polynomial Q comes from outside Coq.                  *)

Local Open Scope C_scope.

Definition coef_at (p : list C) (k : nat) : C := nth k p C0.

Fixpoint zip_with (f : C -> C -> C) (a b : list C) : list C :=
  match a, b with
  | x :: a', y :: b' => f x y :: zip_with f a' b'
  | _, _ => []
  end.

(* a unit complex number with u s p_j = c q_j and u c p_0 + s q_0 = 0 *)
Definition unit_ratio (a b : C) : C :=
  if Rlt_dec 0 (Cmod a) then if Rlt_dec 0 (Cmod b) then a * b ^* / RtoC (Cmod a * Cmod b) else C1 else C1.

(* (c, s, u) of the layer that lowers [P; Q] from degree j to j - 1. When the
   leading pair is zero the trailing pair decides instead. *)
Definition layer_params (p q : list C) (j : nat) : R * R * C :=
  let pj := coef_at p j in let qj := coef_at q j in
  let p0 := coef_at p 0 in let q0 := coef_at q 0 in
  let r := sqrt (Cmod pj ^ 2 + Cmod qj ^ 2)%R in
  let r0 := sqrt (Cmod p0 ^ 2 + Cmod q0 ^ 2)%R in
  if Rlt_dec 0 r then ((Cmod pj / r)%R, (Cmod qj / r)%R, unit_ratio qj pj)
  else if Rlt_dec 0 r0 then ((Cmod q0 / r0)%R, (Cmod p0 / r0)%R, Copp (unit_ratio q0 p0))
  else (1%R, 0%R, C1).

(* one layer: [top; bot] = R^dag [P; Q]; P' = top / z, Q' = bot without z^j *)
Definition strip_step (p q : list C) (j : nat) : (R * R * C) * (list C * list C) :=
  let '(c, s, u) := layer_params p q j in
  let top := zip_with (fun a b => u * RtoC c * a + RtoC s * b) p q in
  let bot := zip_with (fun a b => u * RtoC s * a - RtoC c * b) p q in
  ((c, s, u), (tl top, firstn j bot)).

(* layers for degrees d .. 1 (outermost first) and the base vector (p_0', q_0') *)
Fixpoint strip (d : nat) (p q : list C) : list (R * R * C) * (C * C) :=
  match d with
  | O => ([], (coef_at p 0, coef_at q 0))
  | S d' =>
      let '(l, (p', q')) := strip_step p q d in
      let '(ls, v0) := strip d' p' q' in
      (l :: ls, v0)
  end.

(* the polynomial pair the layers define, evaluated at z: the specification
   for the correctness proof (not used by the compiler) *)
Definition apply_layer (l : R * R * C) (v : C * C) (z : C) : C * C :=
  let '(c, s, u) := l in
  let a := z * fst v in let b := snd v in
  (u ^* * RtoC c * a + u ^* * RtoC s * b, RtoC s * a - RtoC c * b).

Definition gqsp_eval (layers : list (R * R * C)) (v0 : C * C) (z : C) : C * C :=
  fold_right (fun l v => apply_layer l v z) v0 layers.

Local Close Scope C_scope.

(* argument of a complex number (atan2 over all quadrants) *)
Definition carg (z : C) : R :=
  let x := fst z in let y := snd z in
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else if Rlt_dec 0 y then PI / 2 else if Rlt_dec y 0 then - (PI / 2) else 0.

(* complementary polynomial Q with |P|^2 + |Q|^2 = 1 on |z| = 1 for P given by
   real and imaginary coefficient parts; computed outside Coq (untrusted, the
   identity is assumed by the correctness theorem) *)
Parameter gqsp_complement : list R -> list R -> list R * list R.

(* rgate angles: R(th, ph, 0) has cos th = c, sin th = s, e^{i ph} = u^*;
   the base gate R(th_0, ph_0, la)|0> = (p_0', q_0'). Returns
   thetas_0..d ++ phis_0..d ++ [lambda] (index j = layer of degree j). *)
Definition gqsp_angles (re im : list R) : list R :=
  let p := map (fun xy => (fst xy, snd xy)) (combine re im) in
  let '(qre, qim) := gqsp_complement re im in
  let q := map (fun xy => (fst xy, snd xy)) (combine qre qim) in
  let d := (length p - 1)%nat in
  let '(layers, (p0, q0)) := strip d p q in
  let inner := rev layers in                       (* index 0 = degree 1 *)
  let th l := let '(c, s, _) := l in atan2_nn s c in
  let ph l := let '(_, _, u) := l in carg (Cconj u) in
  let la := carg q0 in
  (atan2_nn (Cmod q0) (Cmod p0) :: map th inner)
  ++ ((carg p0 - la) :: map ph inner) ++ [la].

Definition rgate (th ph la : R) (g : nat) : gl :=
  [X g; U1 la g; X g; Ry (-2 * th) g; U1 PI g; X g; U1 ph g; X g].

Record qsp_layout := { sl_idx : list nat; sl_sig : nat; sl_work : list nat }.

Definition qsp_alloc (nbit a : nat) : qsp_layout :=
  {| sl_idx := qrange nbit a; sl_sig := (nbit + a)%nat; sl_work := qrange (nbit + a + 1) (S a) |}.

Definition qsp_nqubits (nbit a : nat) : nat := (nbit + 2 * a + 2)%nat.

(* the Laurent coefficients i^n J_n(tau) (1 - delta), n = k - K for k = 0..2K;
   since J_{-m} = (-1)^m J_m, i^n J_n = i^|n| J_|n| *)
Definition qsp_coeffs (tau delta : R) (K : nat) : list R * list R :=
  let m k := if Nat.leb k K then (K - k)%nat else (k - K)%nat in
  let ks := seq 0 (S (2 * K)) in
  (map (fun k => let re := match Nat.modulo (m k) 4 with 0%nat => 1 | 2%nat => -1 | _ => 0 end in
                 (1 - delta) * re * bessel_j (m k) tau) ks,
   map (fun k => let im := match Nat.modulo (m k) 4 with 1%nat => 1 | 3%nat => -1 | _ => 0 end in
                 (1 - delta) * im * bessel_j (m k) tau) ks).

Definition qsp_segment (nbit : nat) (lp : lowprog) (tau delta : R) (K : nat) (L : qsp_layout) : gl :=
  let '(re, im) := qsp_coeffs tau delta K in
  let ang := gqsp_angles re im in
  let d := (2 * K)%nat in
  let th j := nth j ang 0 in
  let ph j := nth (S d + j) ang 0 in
  let la := nth (2 * S d) ang 0 in
  let g := sl_sig L in
  let W := walk nbit lp (sl_idx L) (sl_work L) [g] in
  prep lp (sl_idx L) ++ rgate (th O) (ph O) la g
  ++ flat_map (fun j => [X g] ++ W ++ [X g] ++ rgate (th j) (ph j) 0 g) (seq 1 d)
  ++ repeat_gl K (inv_gl (walk nbit lp (sl_idx L) (sl_work L) []))
  ++ inv_gl (prep lp (sl_idx L)).

Definition qsp_tau_max : R := 10.

Definition qsp_segments (lp : lowprog) (t : R) : nat :=
  Nat.max 1 (ceilR_N (lcu_lambda lp * t / qsp_tau_max)).

Definition qsp_circuit (err t : R) (nbit : nat) (lp0 : lowprog) : gl :=
  let lp := lcu_terms lp0 in
  let r := qsp_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let delta := err / (4 * INR r) in
  let K := Nat.max 1 (findK_qwalk tau delta) in
  repeat_gl r (qsp_segment nbit lp tau delta K (qsp_alloc nbit (idx_width lp))).

(* ---------------------------------------------------------------------- *)
(* Resource accounting (see QBlueQuantumWalk.v)                            *)

Definition qsp_pieces (err t : R) (nbit : nat) (lp0 : lowprog) : lcu_report :=
  let lp := lcu_terms lp0 in
  let r := qsp_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let delta := err / (4 * INR r) in
  let K := Nat.max 1 (findK_qwalk tau delta) in
  let a := idx_width lp in
  let L := qsp_alloc nbit a in
  let g := sl_sig L in
  (* one controlled-walk step with its signal rotation; angles do not change
     the gate count, so a generic angle stands for all of them *)
  let step := [X g] ++ walk nbit lp (sl_idx L) (sl_work L) [g] ++ [X g] ++ rgate 1 1 0 g in
  let ends := prep lp (sl_idx L) ++ rgate 1 1 1 g ++ inv_gl (prep lp (sl_idx L)) in
  (qsp_nqubits nbit a, r, (2 * K)%nat,
   [(r * (2 * K), step); (r * K, walk nbit lp (sl_idx L) (sl_work L) []); (r, ends)]%nat).

