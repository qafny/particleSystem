(*************************************************************************)
(* QBlueQuantumWalk.v                                                    *)
(* Shared LCU building blocks (SELECT, state preparation, reflections,  *)
(* block encoding, qubitization walk, amplitude amplification) and the   *)
(* quantum-walk simulation method (qubitization walk + Jacobi-Anger LCU, *)
(* Berry, Childs, Kothari 2015).                                         *)
(*                                                                       *)
(* H = sum_j c_j P_j (real c_j, Pauli strings P_j), lambda = sum |c_j|.  *)
(* Qubit layout: system qubits 0 .. nbit-1, registers are lists of       *)
(* qubits (LSB first), `work` is a pool of clean qubits used by Toffoli  *)
(* ladders and always returned clean.                                    *)
(*                                                                       *)
(* Circuits are built as gate lists (`gl`) and turned into a ucom with   *)
(* `to_ucom`. `useq a b` applies a first; lists apply left to right.     *)
(* The other LCU methods are in QBlueTTS_v4.v (Taylor series),           *)
(* QBlueQubitization.v (QSP) and QBlueQSVT.v (QSVT).                     *)
(*************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ratan.
Require Import Coq.Arith.PeanoNat.
Require Import QuantumLib.Complex.
Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
(* last, so its gate names (U, X, H, ...) shadow QBlueSyntax's *)
From SQIR Require Import ExtractionGateSet.
Import ListNotations.

(* Bessel functions J_k(tau) and the smallest K with
   sum_{k > K} 2 |J_k(tau)| < eps; both extracted to OCaml *)
Parameter bessel_j : nat -> R -> R.
Parameter findK_qwalk : R -> R -> nat.

Local Open Scope R_scope.

Definition gl := list (ucom U).

Fixpoint to_ucom (l : gl) : ucom U :=
  match l with
  | [] => SKIP
  | [c] => c
  | c :: rest => useq c (to_ucom rest)
  end.

Definition inv_gl (l : gl) : gl := rev (map invert l).

Fixpoint repeat_gl (k : nat) (l : gl) : gl :=
  match k with O => [] | S k' => l ++ repeat_gl k' l end.

Definition Ry (th : R) (q : nat) : ucom U := U3 th 0 0 q.

(* exact diag(e^{-i phi}, e^{i phi}) = Rz(2 phi) *)
Definition rz2 (phi : R) (q : nat) : gl := [X q; U1 (- phi) q; X q; U1 phi q].

(* controlled Ry *)
Definition cry (th : R) (c t : nat) : gl :=
  [Ry (th / 2) t; CX c t; Ry (- (th / 2)) t; CX c t].

(* atan2 for y >= 0, x >= 0 *)
Definition atan2_nn (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x) else if Rlt_dec 0 y then PI / 2 else 0.

(* min / max with the float comparisons the extraction inlines *)
Definition rmax0 (x : R) : R := if Rle_dec x 0 then 0 else x.
Definition rmin1 (x : R) : R := if Rle_dec x 1 then x else 1.

(* 2 acos(c) for 0 <= c <= 1, i.e. the Ry angle with cos(theta / 2) = c *)
Definition ry_angle_cos (c : R) : R :=
  2 * atan2_nn (sqrt (rmax0 (1 - c * c))) c.

(* ---------------------------------------------------------------------- *)
(* Toffoli ladders and multi-controlled operations                         *)

Fixpoint ladder (prev : nat) (cs work : list nat) : gl * nat :=
  match cs, work with
  | c :: cs', w :: work' =>
      let (u, last) := ladder w cs' work' in (CCX prev c w :: u, last)
  | _, _ => ([], prev)
  end.

(* g c, where qubit c is 1 iff every qubit of ctrls is 1. Needs
   length ctrls - 1 <= length work. *)
Definition mc_apply (ctrls work : list nat) (g : nat -> gl) : gl :=
  match ctrls with
  | [] => []
  | c0 :: cs => let (up, last) := ladder c0 cs work in up ++ g last ++ inv_gl up
  end.

Definition flips (reg : list nat) (v : nat) : gl :=
  flat_map (fun bq => if Nat.testbit v (fst bq) then [] else [X (snd bq)])
           (combine (seq 0 (length reg)) reg).

(* g c, controlled on reg = v and on every qubit of extra being 1 *)
Definition on_value (reg : list nat) (v : nat) (extra work : list nat) (g : nat -> gl) : gl :=
  flips reg v ++ mc_apply (extra ++ reg) work g ++ flips reg v.

(* I - 2|0><0| on reg, controlled on extra *)
Definition refl0 (reg work extra : list nat) : gl :=
  map X reg ++ mc_apply (extra ++ reg) work (fun c => [U1 PI c]) ++ map X reg.

(* ---------------------------------------------------------------------- *)
(* SELECT                                                                  *)

(* controlled Pauli string on system qubits 0 .. nbit-1 *)
Definition cpauli (c nbit : nat) (f : nat -> paulimat) : gl :=
  flat_map (fun i =>
    match f i with
    | paulix => [CX c i]
    | pauliy => [U1 (- (PI / 2)) i; CX c i; U1 (PI / 2) i]
    | pauliz => [H i; CX c i; H i]
    | paulii => []
    end) (seq 0 nbit).

(* SEL = sum_j |j><j| (x) sign(c_j) P_j: Hermitian, SEL^2 = I *)
Definition select (nbit : nat) (terms : lowprog) (idx work extra : list nat) : gl :=
  flat_map (fun jt =>
    let '(j, (c, f)) := jt in
    on_value idx j extra work (fun ctl =>
      cpauli ctl nbit f ++ (if Rlt_dec (fst c) 0 then [U1 PI ctl] else [])))
    (combine (seq 0 (length terms)) terms).

(* ---------------------------------------------------------------------- *)
(* State preparation (Mottonen et al.: uniformly controlled Ry via Gray    *)
(* code, 2^l Ry + 2^l CX per level, no nested controls)                    *)

Definition parity_sign (k : nat) : R := if Nat.even k then 1 else -1.

(* Walsh-Hadamard transform, W[k] = sum_j (-1)^{popcount(j & k)} l[j], for
   length 2^n (top bit = first half): O(m log m) *)
Fixpoint wht (n : nat) (l : list R) : list R :=
  match n with
  | O => l
  | S n' =>
      let h := Nat.pow 2 n' in
      let a := wht n' (firstn h l) in
      let b := wht n' (skipn h l) in
      map (fun xy => fst xy + snd xy) (combine a b) ++ map (fun xy => fst xy - snd xy) (combine a b)
  end.

(* [l[gray 0]; l[gray 1]; ...] for length 2^n: the reflected Gray code visits
   the first half in Gray order, then the second half in reverse Gray order *)
Fixpoint gray_perm (n : nat) (l : list R) : list R :=
  match n with
  | O => l
  | S n' =>
      let h := Nat.pow 2 n' in
      gray_perm n' (firstn h l) ++ rev (gray_perm n' (skipn h l))
  end.

(* bit that changes from gray i to gray (i + 1 mod 2^n): the number of
   trailing zeros of i + 1, or the top bit when wrapping around *)
Fixpoint ctz_aux (fuel k : nat) : nat :=
  match fuel with
  | O => O
  | S f => if Nat.even k then S (ctz_aux f (Nat.div k 2)) else O
  end.
Definition gray_step_bit (n i : nat) : nat :=
  if Nat.eqb (S i) (Nat.pow 2 n) then (n - 1)%nat else ctz_aux 64 (S i).

(* Ry(thetas[v]) on target when ctrls (LSB first) = v *)
Definition ucry (thetas : list R) (target : nat) (ctrls : list nat) : gl :=
  match ctrls with
  | [] => [Ry (nth 0 thetas 0) target]
  | _ =>
      let n := length ctrls in
      let m := Nat.pow 2 n in
      let alphas := map (fun x => x / INR m) (gray_perm n (wht n (firstn m thetas))) in
      flat_map (fun ia =>
        [Ry (snd ia) target; CX (nth (gray_step_bit n (fst ia)) ctrls O) target])
        (combine (seq 0 m) alphas)
  end.

Fixpoint pair_norms (l : list R) : list R :=
  match l with
  | x :: y :: t => sqrt (x * x + y * y) :: pair_norms t
  | [x] => [Rabs x]
  | [] => []
  end.

Fixpoint pair_angles (l : list R) : list R :=
  match l with
  | x :: y :: t => 2 * atan2_nn y x :: pair_angles t
  | [x] => [0]
  | [] => []
  end.

(* rotation angles per level, finest level (target = bit 0) first *)
Fixpoint level_angles (a : nat) (l : list R) : list (list R) :=
  match a with
  | O => []
  | S a' => pair_angles l :: level_angles a' (pair_norms l)
  end.

(* |0> -> sum_v amps[v] |v> on reg (LSB first); amps >= 0, ||amps|| = 1 *)
Definition state_prep (amps : list R) (reg : list nat) : gl :=
  let a := length reg in
  let full := amps ++ List.repeat 0 (Nat.pow 2 a - length amps) in
  let angs := rev (level_angles a full) in          (* coarsest level first *)
  flat_map (fun lvl =>
    ucry (nth lvl angs []) (nth (a - 1 - lvl) reg O) (skipn (a - lvl) reg))
    (seq 0 a).

(* ---------------------------------------------------------------------- *)
(* LCU data and the block encoding                                         *)

Definition coef (t : lowprog_ten) : R := fst (fst t).

(* drop zero terms, pad to at least two terms *)
Definition lcu_terms (lp : lowprog) : lowprog :=
  let nz := filter (fun t => if Rlt_dec 0 (Rabs (coef t)) then true else false) lp in
  match nz with
  | [] => [(C0, fun _ => paulii); (C0, fun _ => paulii)]
  | [t] => [t; (C0, fun _ => paulii)]
  | _ => nz
  end.

Definition lcu_lambda (lp : lowprog) : R := fold_left (fun s t => s + Rabs (coef t)) lp 0.

Definition lcu_amps (lp : lowprog) : list R :=
  let lam := lcu_lambda lp in map (fun t => sqrt (Rabs (coef t) / lam)) lp.

Definition idx_width (lp : lowprog) : nat := Nat.max 1 (Nat.log2_up (length lp)).

Definition prep (lp : lowprog) (idx : list nat) : gl := state_prep (lcu_amps lp) idx.

(* U_BE = PREP^dag SEL PREP, <0|U_BE|0> = H / lambda *)
Definition block_encoding (nbit : nat) (lp : lowprog) (idx work extra : list nat) : gl :=
  prep lp idx ++ select nbit lp idx work extra ++ inv_gl (prep lp idx).

(* qubitization walk Wm = -(2|G><G| - I) SEL, |G> = PREP|0>:
   <G| Wm^k |G> = (-1)^k T_k(H / lambda). extra controls the whole operator. *)
Definition walk (nbit : nat) (lp : lowprog) (idx work extra : list nat) : gl :=
  select nbit lp idx work extra ++ inv_gl (prep lp idx) ++ refl0 idx work extra ++ prep lp idx.

(* one round of oblivious amplitude amplification: <0|A|0> = U / 2 gives
   <0| A R A^dag R A |0> = -U, R = I - 2|0><0| on the ancillas *)
Definition oaa (A : gl) (anc work : list nat) : gl :=
  let R := refl0 anc work [] in A ++ R ++ inv_gl A ++ R ++ A.

(* Ry angle giving amplitude B / 2 on |0> (B <= 2) *)
Definition pad_angle (B : R) : R := ry_angle_cos (rmin1 (B / 2)).

Definition qrange (start len : nat) : list nat := seq start len.

(* ---------------------------------------------------------------------- *)
(* 2. Quantum walk: Jacobi-Anger LCU over powers of the qubitization walk  *)
(*    (Berry, Childs, Kothari 2015)                                        *)
(*    e^{-i tau x} = J_0 + 2 sum (-i)^k J_k T_k(x), T_k = (-1)^k <G|Wm^k|G> *)

Record qwalk_layout := { ql_idx : list nat; ql_outer : list nat; ql_pad : nat; ql_work : list nat }.

Definition qwalk_alloc (nbit a m : nat) : qwalk_layout :=
  let p := (nbit + a + m)%nat in
  {| ql_idx := qrange nbit a; ql_outer := qrange (nbit + a) m; ql_pad := p;
     ql_work := qrange (S p) (a + m) |}.

Definition qwalk_nqubits (nbit a m : nat) : nat := (nbit + 2 * (a + m) + 1)%nat.

Definition ja_beta (tau : R) (K : nat) : list R :=
  bessel_j 0 tau :: map (fun k => 2 * bessel_j k tau) (seq 1 K).

(* <0|A|0> = (1/2) sum_k i^k beta_k <G|Wm^k|G> ~ e^{-i tau H / lambda} / 2 *)
Definition qwalk_segment (nbit : nat) (lp : lowprog) (tau : R) (K : nat) (L : qwalk_layout) : gl :=
  let beta := ja_beta tau K in
  let B := fold_left (fun s b => s + Rabs b) beta 0 in
  let oprep := state_prep (map (fun b => sqrt (Rabs b / B)) beta) (ql_outer L) in
  [Ry (pad_angle B) (ql_pad L)] ++ prep lp (ql_idx L) ++ oprep
  ++ map (fun jq => U1 (PI / 2 * INR (Nat.pow 2 (fst jq))) (snd jq))
         (combine (seq 0 (length (ql_outer L))) (ql_outer L))
  ++ flat_map (fun kb => if Rlt_dec (snd kb) 0
                         then on_value (ql_outer L) (fst kb) [] (ql_work L) (fun c => [U1 PI c])
                         else []) (combine (seq 0 (S K)) beta)
  ++ flat_map (fun jq => repeat_gl (Nat.pow 2 (fst jq))
                           (walk nbit lp (ql_idx L) (ql_work L) [snd jq]))
              (combine (seq 0 (length (ql_outer L))) (ql_outer L))
  ++ inv_gl oprep ++ inv_gl (prep lp (ql_idx L)).

(* the segment without its controlled walk operators (resource accounting) *)
Definition qwalk_segment_rest (nbit : nat) (lp : lowprog) (tau : R) (K : nat) (L : qwalk_layout) : gl :=
  let beta := ja_beta tau K in
  let B := fold_left (fun s b => s + Rabs b) beta 0 in
  let oprep := state_prep (map (fun b => sqrt (Rabs b / B)) beta) (ql_outer L) in
  [Ry (pad_angle B) (ql_pad L)] ++ prep lp (ql_idx L) ++ oprep
  ++ map (fun jq => U1 (PI / 2 * INR (Nat.pow 2 (fst jq))) (snd jq))
         (combine (seq 0 (length (ql_outer L))) (ql_outer L))
  ++ flat_map (fun kb => if Rlt_dec (snd kb) 0
                         then on_value (ql_outer L) (fst kb) [] (ql_work L) (fun c => [U1 PI c])
                         else []) (combine (seq 0 (S K)) beta)
  ++ inv_gl oprep ++ inv_gl (prep lp (ql_idx L)).

Definition qwalk_tau_max : R := 1.

Definition qwalk_segments (lp : lowprog) (t : R) : nat :=
  Nat.max 1 (ceilR_N (lcu_lambda lp * t / qwalk_tau_max)).

Definition qwalk_circuit (err t : R) (nbit : nat) (lp0 : lowprog) : gl :=
  let lp := lcu_terms lp0 in
  let r := qwalk_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let K := Nat.max 1 (findK_qwalk tau (err / (4 * INR r))) in
  let m := Nat.max 1 (Nat.log2_up (S K)) in
  let L := qwalk_alloc nbit (idx_width lp) m in
  let A := qwalk_segment nbit lp tau K L in
  repeat_gl r (oaa A (ql_idx L ++ ql_outer L ++ [ql_pad L]) (ql_work L)).

(* ---------------------------------------------------------------------- *)
(* Resource accounting                                                     *)
(*                                                                         *)
(* Each circuit above is, as a multiset of gates, the union of the pieces  *)
(* below repeated by their multiplicities (an inverse piece has the same   *)
(* gates up to angle signs). The compiler counts every distinct piece once *)
(* and multiplies, so circuits too large to materialize can be counted.    *)
(* Result: (total qubits, segments, polynomial degree / truncation order,  *)
(*          pieces).                                                       *)

Definition lcu_report := (nat * nat * nat * list (nat * gl))%type.

Definition qwalk_pieces (err t : R) (nbit : nat) (lp0 : lowprog) : lcu_report :=
  let lp := lcu_terms lp0 in
  let r := qwalk_segments lp t in
  let tau := lcu_lambda lp * t / INR r in
  let K := Nat.max 1 (findK_qwalk tau (err / (4 * INR r))) in
  let a := idx_width lp in
  let m := Nat.max 1 (Nat.log2_up (S K)) in
  let L := qwalk_alloc nbit a m in
  let R := refl0 (ql_idx L ++ ql_outer L ++ [ql_pad L]) (ql_work L) [] in
  (* 2^m - 1 controlled walks per segment differ only in the control qubit, so
     one stands for all of them, counted on a canonical layout (index register,
     control, then work) that does not move with m *)
  let cw := walk nbit lp (qrange nbit a) (qrange (nbit + a + 1) (S a)) [(nbit + a)%nat] in
  (qwalk_nqubits nbit a m, r, K,
   [(3 * r, qwalk_segment_rest nbit lp tau K L); (3 * r * (Nat.pow 2 m - 1), cw); (2 * r, R)]%nat).


(* ---------------------------------------------------------------------- *)
(* Kept for QBluePEA.v (phase estimation): a walk operator built from given *)
(* PREP and SELECT circuits. The simulation methods use `walk` above.       *)

Definition reflect_ancilla (n : nat) (aux : nat) : ucom U :=
  let anc      := seq 0 n in
  let flip1    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  let multi_cz :=
    fold_right (fun i acc => ExtractionGateSet.control i acc) (U1 PI aux) anc in
  let phase    := useq (useq (X aux) multi_cz) (X aux) in
  let flip2    := fold_left (fun acc i => useq (X i) acc) anc SKIP in
  useq (useq flip1 phase) flip2.

Definition walk_operator (PREP SELECT : ucom U) (n_anc aux : nat) : ucom U :=
  let R0       := reflect_ancilla n_anc aux in
  let PREP_dag := invert PREP in
  let U'       := useq PREP SELECT in
  let U_dag    := invert U' in
  let R_G      := useq (useq PREP_dag R0) PREP in
  let R_Pi     := useq (useq U_dag R0) U' in
  useq R_G R_Pi.

Fixpoint n_copies (n : nat) (g : ucom U) : ucom U :=
  match n with
  | O    => SKIP
  | S n' => useq g (n_copies n' g)
  end.

(* importers have always seen these scopes *)
Global Open Scope R_scope.
Global Open Scope nat_scope.
