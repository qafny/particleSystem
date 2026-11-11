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

(* QSP phase solver, Wx convention.
   Spec: for c = [c_0..c_D], the Chebyshev coefficients of a real polynomial
   f(x) = sum_k c_k T_k(x) of parity p (c_k = 0 unless k = p mod 2) with
   |f| < 1 on [-1,1], qsvt_phases c p = [phi_0..phi_d] where d = D, or D+1
   when D has the wrong parity, phi_k = phi_{d-k}, and
     Re <0| e^{i phi_0 Z} prod_{k=1..d} (W(x) e^{i phi_k Z}) |0> = f(x),
     W(x) = [[x, i sqrt(1-x^2)]; [i sqrt(1-x^2), x]] = e^{i arccos(x) X}.
   Newton iteration on the reduced phases phi_{d/2..d} (Dong, Lin, Ni, Wang,
   "Efficient phase-factor evaluation in quantum signal processing", 2021),
   matching f at the floor(d/2)+1 positive Chebyshev nodes, which determine a
   parity-p polynomial of degree <= d. *)

(* f(x) = sum_k c_k T_k(x), by Clenshaw's recurrence *)
Definition cheb_eval (c : list R) (x : R) : R :=
  let '(b0, b1) := fold_right (fun ck (bb : R * R) => let '(b1, b2) := bb in
                                 (ck + 2 * x * b1 - b2, b1)) (0, 0) c in
  b0 - x * b1.

(* Re <0| e^{i phi_0 Z} prod_k (W(x) e^{i phi_k Z}) |0>; the state (a, b) is
   kept as four reals (Re a, Im a, Re b, Im b) *)
Definition qsp_re (phis : list R) (x : R) : R :=
  match phis with
  | [] => 0
  | p0 :: rest =>
    let s := sqrt (1 - x * x) in
    let step (st : R * R * R * R) (p : R) :=
      let '(ar, ai, br, bi) := st in
      (* (a, b) <- (x a + i s b, i s a + x b) *)
      let ar' := x * ar - s * bi in let ai' := x * ai + s * br in
      let br' := x * br - s * ai in let bi' := x * bi + s * ar in
      (* a <- e^{i p} a, b <- e^{-i p} b *)
      let cp := cos p in let sp := sin p in
      (ar' * cp - ai' * sp, ar' * sp + ai' * cp, br' * cp + bi' * sp, bi' * cp - br' * sp) in
    let '(ar, _, _, _) := fold_left step rest (cos p0, sin p0, 0, 0) in
    ar
  end.

(* the d+1 symmetric phases from the reduced ones phi_{d/2..d} *)
Definition full_phases (red : list R) (d : nat) : list R :=
  if Nat.even d then rev (tl red) ++ red else rev red ++ red.

Definition sub_list (u v : list R) : list R := map (fun ab => fst ab - snd ab) (combine u v).

Definition max_abs (v : list R) : R := fold_left (fun m a => Rmax m (Rabs a)) v 0.

(* Gaussian elimination with partial pivoting on the n x (n+1) augmented
   rows [a_i0 .. a_i(n-1); b_i]; returns x with A x = b *)
Fixpoint gauss_solve (n : nat) (rows : list (list R)) : list R :=
  match n with
  | O => []
  | S n' =>
    let '(ip, _, _) :=
      fold_left (fun (acc : nat * R * nat) r => let '(bi, bv, i) := acc in
                   let v := Rabs (hd 0 r) in
                   if Rlt_dec bv v then (i, v, S i) else (bi, bv, S i))
                rows (O, -1, O) in
    let piv := nth ip rows [] in
    let others := firstn ip rows ++ skipn (S ip) rows in
    let p0 := hd 0 piv in
    let reduced := map (fun r => let f := hd 0 r / p0 in
                          tl (map (fun ab => fst ab - f * snd ab) (combine r piv))) others in
    let xs := gauss_solve n' reduced in
    let dot := fold_left Rplus (map (fun ab => fst ab * snd ab) (combine (firstn n' (tl piv)) xs)) 0 in
    ((nth n piv 0 - dot) / p0) :: xs
  end.

Definition qsp_tol : R := 1 / 1000000000000.   (* 1e-12 *)
Definition qsp_fd_step : R := 1 / 10000000.    (* 1e-7 *)
Definition qsp_maxit : nat := 100.

Definition bump (v : list R) (k : nat) (h : R) : list R :=
  map (fun iv => let '(i, a) := iv in if Nat.eqb i k then a + h else a)
      (combine (seq 0 (length v)) v).

Definition qsp_values (d : nat) (xs red : list R) : list R :=
  map (qsp_re (full_phases red d)) xs.

(* Newton on the reduced phases, with a central-difference Jacobian *)
Fixpoint qsp_newton (fuel d : nat) (xs target red : list R) : list R :=
  match fuel with
  | O => red
  | S fuel' =>
    let res := sub_list (qsp_values d xs red) target in
    if Rlt_dec (max_abs res) qsp_tol then red
    else
      let n := length red in
      let h := qsp_fd_step in
      let cols := map (fun k => map (fun v => v / (2 * h))
                                  (sub_list (qsp_values d xs (bump red k h))
                                            (qsp_values d xs (bump red k (- h)))))
                      (seq 0 n) in
      let rows := map (fun i => map (fun col => nth i col 0) cols ++ [nth i res 0]) (seq 0 n) in
      qsp_newton fuel' d xs target (sub_list red (gauss_solve n rows))
  end.

(* degree and Chebyshev nodes for (c, p) *)
Definition qsp_degree (c : list R) (p : nat) : nat :=
  let dc0 := (length c - 1)%nat in
  if Nat.eqb (Nat.modulo dc0 2) p then dc0 else S dc0.

Definition qsp_nodes (d : nat) : list R :=
  let dt := Nat.div (d + 2) 2 in
  map (fun j => cos ((2 * INR j - 1) * PI / (4 * INR dt))) (seq 1 dt).

Definition qsvt_phases (c : list R) (p : nat) : list R :=
  let d := qsp_degree c p in
  let xs := qsp_nodes d in
  let red0 := repeat 0 (length xs - 1) ++ [PI / 4] in
  full_phases (qsp_newton qsp_maxit d xs (map (cheb_eval c) xs) red0) d.

(* largest |Re P - f| over the nodes; below qsp_tol when Newton converged *)
Definition qsvt_phases_residual (c : list R) (p : nat) (phis : list R) : R :=
  let xs := qsp_nodes (qsp_degree c p) in
  max_abs (sub_list (map (qsp_re phis) xs) (map (cheb_eval c) xs)).

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

(* segments of lambda t_seg <= qsvt_tau_max keep the polynomial degree (and
   the phase computation) bounded for long times; each segment is one OAA'd
   QSVT block *)
Definition qsvt_tau_max : R := 50.

Definition qsvt_segments (lp : lowprog) (t : R) : nat :=
  Nat.max 1 (ceilR_N (lcu_lambda lp * t / qsvt_tau_max)).

(* e^{-iHt} up to a global phase: r segments, error err / r each *)
Definition qsvt_circuit (err t : R) (nbit : nat) (lp0 : lowprog) : gl :=
  let lp := lcu_terms lp0 in
  let r := qsvt_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let e := err / (8 * INR r) in
  let L := qsvt_alloc nbit (idx_width lp) in
  let A := qsvt_segment nbit lp tau e e L in
  repeat_gl r (oaa A (vl_idx L ++ [vl_f L; vl_r L; vl_s L]) (vl_work L)).

(* ---------------------------------------------------------------------- *)
(* Resource accounting (see QBlueQuantumWalk.v)                            *)

Definition qsvt_pieces (err t : R) (nbit : nat) (lp0 : lowprog) : lcu_report :=
  let lp := lcu_terms lp0 in
  let r := qsvt_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let K := findK_qwalk tau (err / (8 * INR r)) in
  let dc := if Nat.even K then K else S K in
  let a := idx_width lp in
  let L := qsvt_alloc nbit a in
  let U := block_encoding nbit lp (vl_idx L) (vl_work L) [] in
  let cU := block_encoding nbit lp (vl_idx L) (vl_work L) [vl_s L] in
  let ph := proj_phase L 1 1 in
  let ends := [H (vl_r L); H (vl_s L); U1 (- (PI / 2)) (vl_s L); H (vl_r L); H (vl_s L)] in
  let R := refl0 (vl_idx L ++ [vl_f L; vl_r L; vl_s L]) (vl_work L) [] in
  (* OAA uses each of the r segments three times *)
  (qsvt_nqubits nbit a, r, S dc,
   [(3 * r * dc, U); (3 * r, cU); (3 * r * (dc + 2), ph); (3 * r, ends); (2 * r, R)]%nat).
