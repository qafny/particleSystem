(*************************************************************************)
(* QBlueQSPCore.v                                                        *)
(* Shared pieces of the QSP phase solvers (Wx convention): Chebyshev     *)
(* evaluation, the QSP polynomial, Chebyshev nodes, symmetric phases,    *)
(* and the Newton refinement. Used by Dong-Lin in QBlueQSVT_updateQSP.v  *)
(* and by qsvt_phases in QBlueQSVT.v.                                    *)
(*                                                                       *)
(* Convention: for phases Phi = [phi_0 .. phi_d],                        *)
(*   U_Phi(x) = e^{i phi_0 Z} prod_{k=1..d} (W(x) e^{i phi_k Z}),        *)
(*   W(x) = [[x, i sqrt(1-x^2)]; [i sqrt(1-x^2), x]] = e^{i arccos(x) X} *)
(* and the solvers find symmetric Phi (phi_k = phi_{d-k}) with           *)
(*   Re <0| U_Phi(x) |0> = f(x) on [-1, 1].                              *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Local Open Scope R_scope.

(* f(x) = sum_k c_k T_k(x), by Clenshaw's recurrence *)
Definition cheb_eval (c : list R) (x : R) : R :=
  let '(b0, b1) := fold_right (fun ck (bb : R * R) => let '(b1, b2) := bb in
                                 (ck + 2 * x * b1 - b2, b1)) (0, 0) c in
  b0 - x * b1.

(* Re <0| U_Phi(x) |0>; the state (a, b) = U_Phi(x)|0> is kept as four reals
   (Re a, Im a, Re b, Im b) *)
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

(* index into the reduced phases of full phase k (inverse of full_phases) *)
Definition red_index (d k : nat) : nat :=
  let h := Nat.div (S d) 2 in       (* number of mirrored entries before red *)
  if Nat.even d then (if Nat.leb (Nat.div d 2) k then k - Nat.div d 2 else Nat.div d 2 - k)
  else (if Nat.leb h k then k - h else h - 1 - k).

Definition sub_list (u v : list R) : list R := map (fun ab => fst ab - snd ab) (combine u v).

Definition max_abs (v : list R) : R := fold_left (fun m a => Rmax m (Rabs a)) v 0.

Definition dot (u v : list R) : R := fold_left Rplus (map (fun ab => fst ab * snd ab) (combine u v)) 0.

(* Euclidean norm. Acceptance tests use it rather than max_abs: in the
   extracted code a NaN entry makes the comparison inside Rmax false, so
   max_abs skips it, while a NaN propagates through the sum here and fails
   any "< tol" test. It is never below max_abs, so the test is no looser. *)
Definition l2 (v : list R) : R := sqrt (dot v v).

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
    ((nth n piv 0 - dot (firstn n' (tl piv)) xs) / p0) :: xs
  end.

Definition qsp_tol : R := 1 / 1000000000000.   (* 1e-12 *)
Definition qsp_fd_step : R := 1 / 10000000.    (* 1e-7 *)
Definition qsp_maxit : nat := 100.

Definition bump (v : list R) (k : nat) (h : R) : list R :=
  map (fun iv => let '(i, a) := iv in if Nat.eqb i k then a + h else a)
      (combine (seq 0 (length v)) v).

Definition qsp_values (d : nat) (xs red : list R) : list R :=
  map (qsp_re (full_phases red d)) xs.

(* Newton on the reduced phases, with a central-difference Jacobian (Dong,
   Lin, Ni, Wang, "Robust iterative method for symmetric quantum signal
   processing in all parameter regimes", SIAM J. Sci. Comput. 2024); returns
   at once when the residual is already below qsp_tol *)
Fixpoint qsp_newton (fuel d : nat) (xs target red : list R) : list R :=
  match fuel with
  | O => red
  | S fuel' =>
    let res := sub_list (qsp_values d xs red) target in
    if Rlt_dec (l2 res) qsp_tol then red
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

(* degree and Chebyshev nodes for (c, p): a parity-p polynomial of degree <= d
   is determined by its values at these floor(d/2)+1 positive nodes *)
Definition qsp_degree (c : list R) (p : nat) : nat :=
  let dc0 := (length c - 1)%nat in
  if Nat.eqb (Nat.modulo dc0 2) p then dc0 else S dc0.

Definition qsp_nodes (d : nat) : list R :=
  let dt := Nat.div (d + 2) 2 in
  map (fun j => cos ((2 * INR j - 1) * PI / (4 * INR dt))) (seq 1 dt).

(* the standard starting point (0, ..., 0, pi/4): Re <0|U|0> = 0 there *)
Definition qsp_start (d : nat) : list R :=
  repeat 0 (length (qsp_nodes d) - 1) ++ [PI / 4].

(* largest |Re P - f| over the nodes *)
Definition qsp_residual (c : list R) (p : nat) (phis : list R) : R :=
  let xs := qsp_nodes (qsp_degree c p) in
  max_abs (sub_list (map (qsp_re phis) xs) (map (cheb_eval c) xs)).
