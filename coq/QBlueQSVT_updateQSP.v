(*************************************************************************)
(* QBlueQSVT_updateQSP.v                                                 *)
(* Two QSP phase solvers for Hamiltonian simulation via QSVT             *)
(*   1. haah_qsp_solver    — Haah 2019 (product decomposition + FFT)    *)
(*   2. donglin_qsp_solver — Dong, Meng, Whaley, Lin 2021 (BFGS opt.)  *)
(* Dong-Lin is defined in Coq and is the solver QBlueQSVT.qsvt_phases  *)
(* uses; Haah is still an unused Parameter (not extracted).            *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ratan.
Require Import Coq.Reals.Rtrigo_def.
From SQIR Require Import ExtractionGateSet.
Import ListNotations.
Require Import QBlue.QBlueQuantumWalk.
Require Import QBlue.QBlueQSPCore.

Open Scope R_scope.
Open Scope nat_scope.


(* ------------------------------------------------------------------ *)
(*  Solver 1: Haah 2019                                                *)
(*  "Product Decomposition of Periodic Functions in QSP"              *)
(*  Quantum 3:190, 2019. https://doi.org/10.22331/q-2019-10-07-190    *)
(*                                                                     *)
(*  Algorithm (Julia notebook, 6 steps):                              *)
(*   1. Jacobi-Anger even Laurent coefficients for cos(tau*x)/2       *)
(*   2. Evaluate A and C = sqrt(1-A^2) at D FFT roots of unity        *)
(*   3. Build 2x2 matrix polynomial F from A and C components         *)
(*   4. FFT F components to get coefficient matrices C[:,:,k]         *)
(*   5. Matrix iteration: extract d+1 phases from C                   *)
(*  Requires BigFloat for large tau; float64 for moderate tau.        *)
(* ------------------------------------------------------------------ *)
Parameter haah_qsp_solver : nat -> R -> R -> list R.


(* ------------------------------------------------------------------ *)
(*  Solver 2: Dong, Meng, Whaley, Lin 2021                            *)
(*  "Efficient Phase-Factor Evaluation in Quantum Signal Processing"  *)
(*  Phys. Rev. A 103, 042419.                                         *)
(*  https://doi.org/10.1103/PhysRevA.103.042419                       *)
(*                                                                     *)
(*  Algorithm (QSPBFGS):                                              *)
(*   1. Target f(x) = cos(tau*x)/2 at Chebyshev nodes x_k            *)
(*   2. Evaluate QSP polynomial P(Φ, x_k) via matrix product         *)
(*   3. Gradient ∂L/∂Φ analytically via forward-backward pass        *)
(*   4. L-BFGS quasi-Newton update of phase vector Φ                 *)
(*  Defined in Coq (no longer an extracted Parameter). Generalized to  *)
(*  any parity-p target f given by Chebyshev coefficients, so QSVT's   *)
(*  cos and sin halves both use it (QBlueQSVT.qsvt_phases).            *)
(*  Symmetric phases, reduced to phi_{d/2..d}; the objective uses the  *)
(*  floor(d/2)+1 positive Chebyshev nodes (QBlueQSPCore.qsp_nodes).    *)
(* ------------------------------------------------------------------ *)

Section DongLin.
Local Open Scope R_scope.

(* 2x2 complex matrices [[a, b]; [c, e]], complex numbers as (re, im) *)
Definition cx := (R * R)%type.
Definition m2 := (cx * cx * cx * cx)%type.

Definition cx_add (u v : cx) : cx := (fst u + fst v, snd u + snd v).
Definition cx_mul (u v : cx) : cx := (fst u * fst v - snd u * snd v, fst u * snd v + snd u * fst v).

Definition m2_mul (m n : m2) : m2 :=
  let '(a1, b1, c1, e1) := m in let '(a2, b2, c2, e2) := n in
  (cx_add (cx_mul a1 a2) (cx_mul b1 c2), cx_add (cx_mul a1 b2) (cx_mul b1 e2),
   cx_add (cx_mul c1 a2) (cx_mul e1 c2), cx_add (cx_mul c1 b2) (cx_mul e1 e2)).

Definition m2_id : m2 := ((1, 0), (0, 0), (0, 0), (1, 0)).

(* signal W(x) = [[x, i s]; [i s, x]], s = sqrt(1 - x^2) *)
Definition w_mat (x : R) : m2 :=
  let s := sqrt (1 - x * x) in ((x, 0), (0, s), (0, s), (x, 0)).

(* R(p) = e^{i p Z} *)
Definition r_mat (p : R) : m2 := ((cos p, sin p), (0, 0), (0, 0), (cos p, - sin p)).

(* the diagonal of dR/dp = i Z e^{i p Z}: i e^{ip} and -i e^{-ip} *)
Definition dr_diag (p : R) : cx * cx := ((- sin p, cos p), (- sin p, - cos p)).

(* forward pass: L_k = R_0 W R_1 W ... R_{k-1} W, the product before R_k *)
Fixpoint prefixes (acc w : m2) (ph : list R) : list m2 :=
  match ph with
  | [] => []
  | p :: rest => acc :: prefixes (m2_mul (m2_mul acc (r_mat p)) w) w rest
  end.

(* backward pass: S_k = W R_{k+1} W ... R_d, the product after R_k *)
Fixpoint suffixes (w : m2) (ph : list R) : list m2 :=
  match ph with
  | [] => []
  | [_] => [m2_id]
  | _ :: ((q :: _) as rest) =>
      let ss := suffixes w rest in
      m2_mul w (m2_mul (r_mat q) (hd m2_id ss)) :: ss
  end.

(* d Re <0|U(x)|0> / d phi_k for every k at one node:
   Re (L_k dR_k S_k)_00 = Re (L00 dR00 S00 + L01 dR11 S10) *)
Definition node_grad (ph : list R) (x : R) : list R :=
  let w := w_mat x in
  map (fun t => let '(p, (l, s)) := t in
         let '(l00, l01, _, _) := l in let '(s00, _, s10, _) := s in
         let '(d0, d1) := dr_diag p in
         fst (cx_add (cx_mul l00 (cx_mul d0 s00)) (cx_mul l01 (cx_mul d1 s10))))
      (combine ph (combine (prefixes m2_id w ph) (suffixes w ph))).

(* objective 1/2 sum_k (Re U(x_k) - f(x_k))^2 on the reduced phases, with the
   norm of the node errors (QBlueQSPCore.l2: NaN-safe in the stop test) *)
Definition dl_eval (d : nat) (xs target red : list R) : R * R :=
  let e := sub_list (qsp_values d xs red) target in (dot e e / 2, l2 e).

(* gradient with respect to the reduced phases: each full phase k feeds
   reduced phase red_index d k *)
Definition dl_grad (d : nat) (xs target red : list R) : list R :=
  let ph := full_phases red d in
  let e := sub_list (qsp_values d xs red) target in
  let gfull := fold_left (fun acc ex => let '(ek, x) := ex in
                            map (fun ab => fst ab + ek * snd ab) (combine acc (node_grad ph x)))
                         (combine e xs) (repeat 0 (length ph)) in
  map (fun i => fold_left Rplus
                  (map (fun kg => let '(k, g) := kg in if Nat.eqb (red_index d k) i then g else 0)
                       (combine (seq 0 (length gfull)) gfull)) 0)
      (seq 0 (length red)).

Definition axpy (a : R) (x y : list R) : list R := map (fun ab => a * fst ab + snd ab) (combine x y).

(* L-BFGS two-loop recursion; history newest first as (s, y, 1 / (s.y));
   returns r ~ H^{-1} g, the step is -r *)
Definition two_loop (g : list R) (hist : list (list R * list R * R)) : list R :=
  let '(q, alphas) :=
    fold_left (fun (qa : list R * list R) h =>
                 let '(q, al) := qa in let '(s, y, rho) := h in
                 let a := rho * dot s q in (axpy (- a) y q, al ++ [a]))
              hist (g, []) in
  let gamma := match hist with (s, y, _) :: _ => dot s y / dot y y | [] => 1 end in
  fold_left (fun r hay => let '((s, y, rho), a) := hay in axpy (a - rho * dot y r) s r)
            (rev (combine hist alphas)) (map (fun v => gamma * v) q).

(* backtracking Armijo line search: halve the step up to fuel times *)
Fixpoint armijo (fuel : nat) (d : nat) (xs target x r : list R) (f0 gr step : R)
  : option (list R * R * R) :=
  match fuel with
  | O => None
  | S fuel' =>
    let x' := axpy (- step) r x in
    let '(f', m') := dl_eval d xs target x' in
    if Rle_dec f' (f0 - step * gr / 10000) then Some (x', f', m')
    else armijo fuel' d xs target x r f0 gr (step / 2)
  end.

Definition dl_hist_size : nat := 10.
Definition dl_maxit : nat := 500.

(* Ian's L-BFGS loop. Pairs with s.y <= 0 are dropped (they would make the
   inverse-Hessian estimate indefinite); a non-descent direction or a failed
   line search restarts from an empty history, and a failed search with an
   empty history stops. *)
Fixpoint dl_lbfgs (fuel d : nat) (xs target x g : list R) (f m : R)
         (hist : list (list R * list R * R)) : list R :=
  match fuel with
  | O => x
  | S fuel' =>
    if Rlt_dec m qsp_tol then x
    else
      let r0 := two_loop g hist in
      let '(r, hist) := if Rlt_dec 0 (dot g r0) then (r0, hist) else (g, []) in
      let step := match hist with [] => 1 / 10 | _ => 1 end in
      match armijo 30 d xs target x r f (dot g r) step with
      | Some (x', f', m') =>
          let g' := dl_grad d xs target x' in
          let s := sub_list x' x in let y := sub_list g' g in
          let sy := dot s y in
          let hist' := if Rlt_dec (1 / 1000000000000) sy
                       then firstn dl_hist_size ((s, y, 1 / sy) :: hist) else hist in
          dl_lbfgs fuel' d xs target x' g' f' m' hist'
      | None =>
          match hist with
          | [] => x
          | _ => dl_lbfgs fuel' d xs target x g f m []
          end
      end
  end.

(* reduced phases for the parity-p target with Chebyshev coefficients c,
   from the standard start (0, ..., 0, pi/4) *)
Definition donglin_reduced (c : list R) (p : nat) : list R :=
  let d := qsp_degree c p in
  let xs := qsp_nodes d in
  let target := map (cheb_eval c) xs in
  let x0 := qsp_start d in
  let '(f0, m0) := dl_eval d xs target x0 in
  dl_lbfgs dl_maxit d xs target x0 (dl_grad d xs target x0) f0 m0 [].

Definition donglin_phases (c : list R) (p : nat) : list R :=
  full_phases (donglin_reduced c p) (qsp_degree c p).

(* Chebyshev coefficients of cos(tau x)/2 up to T_d (Jacobi-Anger) *)
Definition cos_half_cheb (d : nat) (tau : R) : list R :=
  map (fun j => if Nat.eqb j 0 then bessel_j 0 tau / 2
                else if Nat.even j then (if Nat.even (Nat.div j 2) then 1 else -1) * bessel_j j tau
                else 0)
      (seq 0 (S d)).

End DongLin.

(* the original interface: d+1 phases for cos(tau x)/2 (d even) *)
Definition donglin_qsp_solver (d : nat) (tau err : R) : list R :=
  donglin_phases (cos_half_cheb d tau) 0.


Section QSVTCircuit.

(* Projector-controlled phase shift on n ancilla qubits; aux is scratch.
   Implements e^{i*phi*(I - |0...0><0...0|)} on the ancilla register. *)
Definition reflect_ancilla_phase (n aux : nat) (phi : R)
    : ucom ExtractionGateSet.U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz :=
    fold_right (fun i acc => ExtractionGateSet.control i acc) (U1 phi aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

(* QSVT sequence: phi_0 . SELECT . phi_1 . SELECT . ... . SELECT . phi_d
   For d+1 phases and d SELECT applications, implements a degree-d
   polynomial in the block-encoding of H/lambda. *)
Fixpoint qsvt_sequence (phis : list R) (select : ucom ExtractionGateSet.U)
    (n_anc aux : nat) : ucom ExtractionGateSet.U :=
  match phis with
  | []        => SKIP
  | [phi]     => reflect_ancilla_phase n_anc aux phi
  | phi :: rest =>
      useq (reflect_ancilla_phase n_anc aux phi)
           (useq select (qsvt_sequence rest select n_anc aux))
  end.

(* Polynomial degree: K (the Bessel order: the Chebyshev tail of cos(tau x)
   beyond T_K is below err), rounded up to even. cos(tau x)/2 is even, and a
   degree-d QSP polynomial has the parity of d, so d must be even (the old
   2K + 1 could never fit it).
   Returns the number of SELECT applications; haah/donglin return d+1 phases. *)
Definition findDegree_qsvt (tau err : R) : nat :=
  let K := findK_qwalk tau err in
  Nat.max 2 (if Nat.even K then K else S K).


(* QSVT circuit using Haah 2019 phase solver.
   Use for moderate tau (lambda*t). May lose accuracy for large tau
   if the OCaml implementation uses float64 instead of BigFloat. *)
Definition build_qsvt_circuit_haah
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let phis     := haah_qsp_solver d tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence phis select n_anc aux) prep_dag).

(* QSVT circuit using Dong-Lin 2021 phase solver.
   Numerically stable for any tau in float64.
   Use for large tau or when high accuracy is required. *)
Definition build_qsvt_circuit_donglin
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  let d        := findDegree_qsvt tau err in
  let phis     := donglin_qsp_solver d tau err in
  let prep_dag := invert inner_prep in
  useq inner_prep (useq (qsvt_sequence phis select n_anc aux) prep_dag).

(* Default: use Dong-Lin 2021 (more numerically stable in float64). *)
Definition build_qsvt_circuit
    (inner_prep select : ucom ExtractionGateSet.U)
    (tau err : R) (n_anc aux : nat)
    : ucom ExtractionGateSet.U :=
  build_qsvt_circuit_donglin inner_prep select tau err n_anc aux.

End QSVTCircuit.