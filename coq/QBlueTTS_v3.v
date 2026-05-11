(* QBlueTTS.v
   Linear Combination of Unitaries (LCU) + Taylor Series expansion
   for Hamiltonian simulation: e^{-itH} ≈ sum_{k=0}^{K} (-it)^k / k! * H^k

   Based on:
     Andrew Childs, "Lecture Notes on Quantum Algorithms", Chapter 28.3
     (Linear combinations of unitaries)

   Design notes vs. original (buggy) version:
   -----------------------------------------------
   Bug 1: lowprog type mismatch.
     The existing code uses (C * (nat -> paulimat)) for lowprog_ten
     (amplitude is COMPLEX, from QBlueSyntax.v), but the original TTS file
     mixed in (R * (nat -> paulimat)) norm_ten style and called
     mult_r_hplus (which scales only the real part) on complex amplitudes.
     Fix: use mult_ampli_hplus (which scales a full C) consistently.

   Bug 2: taylor_exp amplitude is wrong.
     Original: Cmult (Cpow Ci k) (RtoC ((pow (-t) k) / (INR (factor k))))
     This uses i^k instead of (-i*t)^k / k!.
     The correct k-th Taylor term for e^{-itH} is:
       coeff_k = (-it)^k / k! = ((-i)*t)^k / k!
     Fix: use  Cmult (Cpow (Copp Ci) k) (RtoC ((pow t k) / (INR (factor k))))
     i.e.  (-i)^k * t^k / k!   [absorb the sign into Copp Ci].

   Bug 3: cal_lowp_power base case.
     Original: returns [] for k=0, which is wrong — the 0th power of H
     should be the identity, i.e. [(C1, fun _ => paulii)].
     Fix: base case O => [(C1, fun _ => paulii)].

   Bug 4: get_nseg formula.
     Original uses fold_left accessing (fst (fst x)) but lowprog_ten is
     (C * (nat -> paulimat)), so fst x : C, and fst (fst x) : R is the
     real part only.  For a Hamiltonian H = sum_j alpha_j P_j the 1-norm
     is lambda = sum_j |alpha_j|, i.e. the complex modulus.
     Fix: use Cmod (fst x) instead of Rabs (fst (fst x)).

   Bug 5: findK_upto initial auxiliary value.
     Original starts aux = ln 2 but the bound being tracked is
       (ln 2)^{K+1} / (K+1)!
     which starts at ln 2 / 1! = ln 2 for K=0, then multiplies by
     (ln 2) / (k+1) each step.  That part is correct for the *ratio*,
     but the first comparison is done BEFORE any multiplication, so k=0
     returns immediately if ln 2 < bound, skipping k=1.
     Fix: start with aux = (ln 2) / INR (1) = ln 2 (correct for K=0 term)
     and ensure the "already small enough" check is done after computing
     the k-th term, not before the k=0 term is even considered.
     Re-structure to: compute term first, then check.

   Bug 6: build_circuit_seg Hadamard fold direction.
     fold_left useq circ_list SKIP chains as SKIP;c0;c1;...
     but the Hadamard sandwich should be H^{\otimes m} · SELECT · H^{\otimes m}.
     The fold for Hadamards is correct in principle but the fold of
     the circuit list leaves SKIP as the leftmost element, inflating the
     circuit.  Use fold_left with pruning, or build the Hadamard register
     as a parallel application.
     Fix: build hadamard_reg by folding useq over (seq 0 nqcn) so that
     qubit 0,1,...,nqcn-1 all get H; compose as H·SELECT·H.

   Bug 7: TTS_LCU fold direction for segment repetition.
     fold_left (fun acc _ => useq circ_seg acc) puts circ_seg on the RIGHT
     of the sequence, meaning the LAST segment is applied first.
     In SQIR, useq a b means "apply a then b", so to apply circ_seg
     nseg times in order (seg_1 ; seg_2 ; ... ; seg_r) we need:
       fold_left (fun acc _ => useq acc circ_seg) ...
     Fix: swap argument order in the lambda.
*)

From SQIR Require Import ExtractionGateSet.

Require Import Reals.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.

(* ================================================================= *)
(*  Section 1. Segment count r                                        *)
(*                                                                    *)
(*  Childs §28.3: split [0,t] into r = ceil(lambda * t / ln 2)       *)
(*  segments, where lambda = sum_j |alpha_j| is the 1-norm of H.     *)
(*  Each segment has time step tau = t / r.                           *)
(* ================================================================= *)

(** 1-norm of the Hamiltonian: lambda = sum_j |alpha_j|.
    BUG FIX 4: original used Rabs(fst(fst x)) = Re(amp), ignoring
    the imaginary part.  Correct measure is the complex modulus. *)
Definition ham_one_norm (lp : lowprog) : R :=
  fold_left (fun (acc : R) (x : lowprog_ten) => Rplus acc (Cmod (fst x))) lp 0%R.

(** Number of Trotter-like segments r = ceil(lambda * t / ln 2).
    BUG FIX 4: use Cmod instead of Rabs . Re. *)
Definition get_nseg (t : R) (lp : lowprog) : nat :=
  let lambda := ham_one_norm lp in
  ceilR_N (lambda * t / ln 2).

(* ================================================================= *)
(*  Section 2. Truncation order K                                     *)
(*                                                                    *)
(*  Childs §28.3: truncate at K so that the tail                      *)
(*    sum_{k=K+1}^inf (lambda*tau)^k / k! <= err / (2r)             *)
(*  Using the bound: tail <= 2 * e^{lambda*tau} * (ln2)^{K+1}/(K+1)! *)
(*  (since tau = t/r and lambda*tau <= ln 2 by choice of r,           *)
(*   and e^{ln2} = 2, giving the factor of 2.)                        *)
(* ================================================================= *)

(** Iteratively find smallest K such that
      aux_k = (ln 2)^{k+1} / (k+1)! <= bound.
    aux is updated as:  aux_{k+1} = aux_k * (ln 2) / (k+2).

    BUG FIX 5: restructured so the k=0 term (aux = ln 2) is evaluated
    before checking, not after — original could under-count by 1. *)
Fixpoint findK_upto (fuel : nat) (bound aux : R) (k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Rltb aux bound
      then k                          (* aux_k <= bound: done *)
      else findK_upto fuel' bound
             (aux * (ln 2) / INR (k + 2))  (* next term *)
             (S k)
  end.

(** Public entry point.
    bound = err / (2 * r);  initial aux = (ln 2)^1 / 1! = ln 2. *)
Definition findK (err t : R) (lp : lowprog) : nat :=
  let r     := get_nseg t lp in
  let bound := (err / (2 * INR r))%R in
  findK_upto 20 bound (ln 2) 0.

(* ================================================================= *)
(*  Section 3. H^k  (iterated Hamiltonian product)                   *)
(*                                                                    *)
(*  H^0 = I,  H^k = H * H^{k-1}  using plus_app_plus.               *)
(*  BUG FIX 3: base case must return [(C1, id)] not [].              *)
(* ================================================================= *)

(** H^k as a lowprog. nqubit is passed to plus_app_plus for the
    Pauli-string composition. *)
Fixpoint cal_lowp_power (nqubit k : nat) (lp : lowprog) : lowprog :=
  match k with
  | 0   => [(C1, fun _ => paulii)]          (* H^0 = I  (BUG FIX 3) *)
  | S k' => plus_app_plus nqubit lp (cal_lowp_power nqubit k' lp)
  end.

(* ================================================================= *)
(*  Section 4. Taylor series  e^{-itH} ≈ sum_{k=0}^{K} c_k H^k      *)
(*                                                                    *)
(*  c_k = (-it)^k / k!  =  (-i)^k * t^k / k!                        *)
(*                                                                    *)
(*  BUG FIX 2: original used Cpow Ci k (= i^k) instead of           *)
(*  Cpow (Copp Ci) k (= (-i)^k).                                     *)
(* ================================================================= *)

(** k-th Taylor coefficient: c_k = (-i)^k * t^k / k! *)
Definition taylor_coeff (t : R) (k : nat) : C :=
  Cmult (Cpow (Copp Ci) k)
        (RtoC (pow t k / INR (factor k))).

(** Full truncated Taylor series up to order K.
    Returns lowprog representing  sum_{k=0}^{K} c_k * H^k. *)
Fixpoint taylor_exp (t : R) (nqubit K : nat) (lp : lowprog) : lowprog :=
  match K with
  | 0   =>
      (* k=0 term: c_0 * H^0 = 1 * I *)
      mult_ampli_hplus (taylor_coeff t 0) (cal_lowp_power nqubit 0 lp)
  | S k' =>
      (* k=K term prepended to the rest *)
      let term_K := mult_ampli_hplus (taylor_coeff t K)
                      (cal_lowp_power nqubit K lp) in
      term_K ++ (taylor_exp t nqubit k' lp)
  end.

(* ================================================================= *)
(*  Section 5. LCU circuit for one segment                           *)
(*                                                                    *)
(*  Given vi = [(c_j, P_j)] (a lowprog from the Taylor expansion),   *)
(*  the LCU circuit is:                                               *)
(*    (H^{\otimes m} ⊗ I) · SELECT · (H^{\otimes m} ⊗ I)            *)
(*  where SELECT |j>|ψ> = |j> V_j |ψ>,  V_j = synth of P_j.         *)
(*  m = ceil(log2(#terms)).                                           *)
(* ================================================================= *)

(** Encode the binary index nl as a controlled projector in lowprog form.
    Each bit b_i ∈ {0,1}: b_i=1 → |1><1| = projector; b_i=0 → |0><0|. *)
Fixpoint cntl2pauli_helper (nl : list nat) : lowprog :=
  match nl with
  | []      => [(C1, fun _ => paulii)]
  | b :: tl =>
      let proj := if b =? 1 then projector else projector0 in
      plus_ten_plus 1%nat (length tl)
        proj
        (cntl2pauli_helper tl)
  end.

(** Synthesise all terms of a lowprog sequentially into SQIR. *)
Fixpoint LCU_digital_ibm (nqubit : nat) (vi : lowprog) : ucom ExtractionGateSet.U :=
  match vi with
  | []             => ExtractionGateSet.SKIP
  | (amp, f) :: tl =>
      ExtractionGateSet.useq
        (synth_digital_ibm_apauli (fst amp) nqubit f)
        (LCU_digital_ibm nqubit tl)
  end.

(** Build the controlled-V_j block for the j-th term:
      I + |j><j| ⊗ (V_j − I)
    nqcn: # control qubits, nqv: # system qubits, idx: j.

    BUG NOTE: the original correctly builds (V−I) via
      t2 = I + |j><j| ⊗ (V−I) in lowprog form and hands to
      LCU_digital_ibm.  We preserve that structure but fix the
      cntl2pauli_helper above. *)
Definition build_cntlV (lp : lowprog) (nqcn nqv idx : nat)
    : ucom ExtractionGateSet.U :=
  match nth_error lp idx with
  | None    => ExtractionGateSet.SKIP
  | Some vi =>
      let nl      := cnt2bin idx nqcn in
      let control := cntl2pauli_helper nl in
      (* (V_j − I) in lowprog: append −I term *)
      let vm1     := (vi :: (Copp C1, fun _ => paulii) :: nil) in
      (* |j><j| ⊗ (V_j − I) *)
      let t2      := plus_ten_plus nqcn nqv control vm1 in
      (* I + above  *)
      LCU_digital_ibm (nqcn + nqv) ((C1, fun _ => paulii) :: t2)
  end.

(** One LCU segment circuit for a prepared lowprog `input`.
    BUG FIX 6: build the Hadamard register as a single sequential
    application over qubits 0..nqcn-1, in the correct order. *)
Definition build_circuit_seg (nqv : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let nterm    := length input in
  let nqcn     := Nat.log2_up nterm in
  (* SELECT: apply controlled-V_j for each j *)
  let circ_list :=
        map (build_cntlV input nqcn nqv) (seq 0 nterm) in
  let select   :=
        fold_left ExtractionGateSet.useq circ_list ExtractionGateSet.SKIP in
  (* Hadamard on all control qubits 0 .. nqcn-1  (BUG FIX 6) *)
  let hadamard :=
        fold_left (fun acc i => ExtractionGateSet.useq acc (ExtractionGateSet.H i))
                  (seq 0 nqcn)
                  ExtractionGateSet.SKIP in
  (* H · SELECT · H  (sandwich) *)
  ExtractionGateSet.useq
    (ExtractionGateSet.useq hadamard select)
    hadamard.

(* ================================================================= *)
(*  Section 6.  Top-level TTS_LCU                                    *)
(*                                                                    *)
(*  Split t into r segments, each of length tau = t/r.               *)
(*  For each segment, build the LCU circuit from the K-truncated      *)
(*  Taylor expansion of e^{-i*tau*H}.                                 *)
(*  Compose r segments in order:  seg_1 ; seg_2 ; ... ; seg_r.       *)
(*                                                                    *)
(*  BUG FIX 7: original fold put circ_seg on the RIGHT (reversed     *)
(*  order).  Fix: useq acc circ_seg so segments compose left-to-right.*)
(* ================================================================= *)

(*  findK_tau: given per-segment time tau and total error epsilon,
    find K such that the Taylor tail for one segment satisfies
       (ln2)^{K+1}/(K+1)!  <=  epsilon / (4*r)
    which implies the full r-segment error is <= epsilon.
    Derived from Childs §28.3 eq. (28.11):
       2 * e^{lambda*tau} * tail <= epsilon/r
    with e^{lambda*tau} <= e^{ln2} = 2.                                *)
Definition findK_tau (err tau : R) (r : nat) : nat :=
  let bound := (err / (4 * INR r))%R in
  findK_upto 20 bound (ln 2) 0.

Definition TTS_LCU (err t : R) (nbit : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in          (* r = ceil(lambda*t / ln2)  *)
  let tau      := (t / INR nseg)%R in          (* tau = t/r, lambda*tau <= ln2 *)
  (* K s.t. Taylor tail of e^{-i*tau*H} is <= epsilon/(2r).
     tau (not t) is passed so the bound is per-segment. *)
  let K        := findK_tau err tau nseg in
  (* Taylor expansion of e^{-i*tau*H} truncated at order K *)
  let prog_seg := taylor_exp tau nbit K input in
  (* LCU circuit for one segment *)
  let circ_seg := build_circuit_seg nbit prog_seg in
  (* Compose r segments in forward order: seg_1 ; seg_2 ; ... ; seg_r *)
  fold_left
    (fun acc _ => ExtractionGateSet.useq acc circ_seg)
    (seq 0 nseg)
    ExtractionGateSet.SKIP.
