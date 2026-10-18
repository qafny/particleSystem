(*************************************************************************)
(* QBlueQSVT.v                                                           *)
(* QSVT (Gilyen, Su, Low, Wiebe 2019): projector phases on the block   *)
(* encoding, cos and sin combined by LCU, one round of amplitude        *)
(* amplification.                                                       *)
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
(* 4. QSVT (Gilyen, Su, Low, Wiebe 2019): projector phases on the block    *)
(*    encoding; cos and sin combined by LCU, then one OAA round.           *)

(* symmetric QSP phases (Wx convention) for the real polynomial with the
   given Chebyshev coefficients and parity: Re P = f *)
Parameter qsvt_phases : list R -> nat -> list R.

(* Wx phases -> phases of e^{i phi (2 Pi - I)} around a Hermitian block
   encoding; <0|U_Phi|0> = i^d P(x) in this convention *)
Definition wx_to_reflection (ph : list R) : list R :=
  let d := length ph in
  map (fun kp => let '(k, p) := kp in
                 if Nat.eqb k 0 || Nat.eqb k (d - 1) then p + PI / 4 else p + PI / 2)
      (combine (seq 0 d) ph).

Record qsvt_layout := { vl_idx : list nat; vl_f : nat; vl_r : nat; vl_s : nat; vl_work : list nat }.

Definition qsvt_alloc (nbit a : nat) : qsvt_layout :=
  {| vl_idx := qrange nbit a; vl_f := (nbit + a)%nat; vl_r := (nbit + a + 1)%nat;
     vl_s := (nbit + a + 2)%nat; vl_work := qrange (nbit + a + 3) (a + 3) |}.

Definition qsvt_nqubits (nbit a : nat) : nat := (nbit + 2 * a + 6)%nat.

(* e^{i psi (2 Pi - I)}, Pi = |0><0|_idx, psi = pa + pb if s = 0 else pa - pb;
   the sign of psi flips when r = 1 *)
Definition proj_phase (L : qsvt_layout) (pa pb : R) : gl :=
  let idx := vl_idx L in let f := vl_f L in let r := vl_r L in let s := vl_s L in
  let flag := map X idx ++ mc_apply idx (vl_work L) (fun c => [CX c f]) ++ map X idx in
  flag ++ [CX r f] ++ rz2 pa f ++ [CX s f] ++ rz2 pb f ++ [CX s f] ++ [CX r f] ++ flag.

Definition cheb_cos (tau : R) (K : nat) : list R :=
  map (fun k => if Nat.eqb k 0 then bessel_j 0 tau
                else if Nat.even k then 2 * parity_sign (Nat.div k 2) * bessel_j k tau else 0)
      (seq 0 (S K)).

Definition cheb_sin (tau : R) (K : nat) : list R :=
  map (fun k => if Nat.even k then 0 else 2 * parity_sign (Nat.div k 2) * bessel_j k tau)
      (seq 0 (S K)).

(* <0|A|0> ~ (1 - eta) i^dc e^{-i tau H / lambda} / 2 *)
Definition qsvt_segment (nbit : nat) (lp : lowprog) (tau eta delta : R) (L : qsvt_layout) : gl :=
  let K := findK_qwalk tau delta in
  let dc := if Nat.even K then K else S K in
  let pc := wx_to_reflection (qsvt_phases (map (fun c => (1 - eta) * c) (cheb_cos tau dc)) 0) in
  let ps0 := wx_to_reflection (qsvt_phases (map (fun c => (1 - eta) * c) (cheb_sin tau (S dc))) 1) in
  (* the odd branch gets an extra -i so both branches carry i^dc *)
  let ps := match ps0 with [] => [] | p :: rest => (p - PI / 2) :: rest end in
  let U := block_encoding nbit lp (vl_idx L) (vl_work L) [] in
  let cU := block_encoding nbit lp (vl_idx L) (vl_work L) [vl_s L] in
  let r := vl_r L in let s := vl_s L in
  [H r; H s; U1 (- (PI / 2)) s]
  ++ flat_map (fun k =>
       let psc := if Nat.leb k dc then nth k pc 0 else 0 in
       let pss := nth k ps 0 in
       proj_phase L ((psc + pss) / 2) ((psc - pss) / 2)
       ++ (if Nat.ltb k dc then U else if Nat.eqb k dc then cU else []))
     (seq 0 (dc + 2))
  ++ [H r; H s].

Definition qsvt_circuit (err t : R) (nbit : nat) (lp0 : lowprog) : gl :=
  let lp := lcu_terms lp0 in
  let tau := lcu_lambda lp * t in
  let L := qsvt_alloc nbit (idx_width lp) in
  let A := qsvt_segment nbit lp tau (err / 8) (err / 8) L in
  oaa A (vl_idx L ++ [vl_f L; vl_r L; vl_s L]) (vl_work L).

(* ---------------------------------------------------------------------- *)
(* Resource accounting (see QBlueQuantumWalk.v)                            *)

Definition qsvt_pieces (err t : R) (nbit : nat) (lp0 : lowprog) : lcu_report :=
  let lp := lcu_terms lp0 in
  let tau := lcu_lambda lp * t in
  let K := findK_qwalk tau (err / 8) in
  let dc := if Nat.even K then K else S K in
  let a := idx_width lp in
  let L := qsvt_alloc nbit a in
  let U := block_encoding nbit lp (vl_idx L) (vl_work L) [] in
  let cU := block_encoding nbit lp (vl_idx L) (vl_work L) [vl_s L] in
  let ph := proj_phase L 1 1 in
  let ends := [H (vl_r L); H (vl_s L); U1 (- (PI / 2)) (vl_s L); H (vl_r L); H (vl_s L)] in
  let R := refl0 (vl_idx L ++ [vl_f L; vl_r L; vl_s L]) (vl_work L) [] in
  (* OAA uses the segment three times *)
  (qsvt_nqubits nbit a, 1%nat, S dc,
   [(3 * dc, U); (3, cU); (3 * (dc + 2), ph); (3, ends); (2, R)]%nat).
