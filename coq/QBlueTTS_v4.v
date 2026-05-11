(* Define the Taylor series simulation and LCU (Linear Combination of Unitaries) *)
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSynthDigital.


(* Use "Lecture Notes on Quantum Algorithms" by Andrew M. Childs, Chapter 28.3
   lambda = 1-norm of H = sum_j |alpha_j|
   r = ceil(lambda * t / ln 2); tau = t / r so that lambda * tau <= ln 2
   K = truncation order s.t. (ln2)^{K+1}/(K+1)! <= err / (4 * r) *)
Definition ham_one_norm (lp : lowprog) : R :=
  fold_left (fun (acc : R) (x : lowprog_ten) => Rplus acc (Cmod (fst x))) lp 0%R.


Definition get_nseg (t : R) (lp : lowprog) : nat :=
  let lambda := ham_one_norm lp in
  ceilR_N (lambda * t / ln 2).


(* Find smallest K s.t. (ln2)^{K+1}/(K+1)! <= bound.
   aux tracks the current term value; fuel bounds recursion depth. *)
Fixpoint findK_upto (fuel : nat) (bound aux : R) (k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Rltb aux bound then k
      else findK_upto fuel' bound (aux * (ln 2) / INR (k + 2)) (S k)
  end.

(* r segments, per-segment bound = err / (4 * r) from Childs eq. (28.11)
   since e^{lambda*tau} <= e^{ln2} = 2, giving factor of 4 in denominator *)
Definition findK_tau (err : R) (r : nat) : nat :=
  let bound := (err / (4 * INR r))%R in
  findK_upto 20 bound (ln 2) 0.


(* H^0 = I, H^k = H * H^{k-1} via plus_app_plus *)
Fixpoint cal_lowp_power (nqubit k : nat) (lp : lowprog) : lowprog :=
  match k with
  | 0 => [(C1, fun _ => paulii)]
  | S k' => plus_app_plus nqubit lp (cal_lowp_power nqubit k' lp)
  end.


(* k-th Taylor coefficient: c_k = (-i)^k * t^k / k! *)
Definition taylor_coeff (t : R) (k : nat) : C :=
  Cmult (Cpow (Copp Ci) k) (RtoC (pow t k / INR (factor k))).

(* Truncated Taylor series sum_{k=0}^{K} c_k * H^k as lowprog *)
Fixpoint taylor_exp (t : R) (nqubit K : nat) (lp : lowprog) : lowprog :=
  match K with
  | 0 => mult_ampli_hplus (taylor_coeff t 0) (cal_lowp_power nqubit 0 lp)
  | S k' =>
      let term_K := mult_ampli_hplus (taylor_coeff t K) (cal_lowp_power nqubit K lp) in
      term_K ++ taylor_exp t nqubit k' lp
  end.


(* Binary index nl encoded as tensor product of projectors for SELECT oracle *)
Fixpoint cntl2pauli_helper (nl : list nat) : lowprog :=
  match nl with
  | [] => [(C1, fun _ => paulii)]
  | b :: tl =>
      let proj := if b =? 1 then projector else projector0 in
      plus_ten_plus 1%nat (length tl) proj (cntl2pauli_helper tl)
  end.

(* Synthesise lowprog terms sequentially into SQIR circuit *)
Fixpoint LCU_digital_ibm (nqubit : nat) (vi : lowprog) : ucom ExtractionGateSet.U :=
  match vi with
  | [] => ExtractionGateSet.SKIP
  | (amp, f) :: tl =>
      ExtractionGateSet.useq
        (synth_digital_ibm_apauli (fst amp) nqubit f)
        (LCU_digital_ibm nqubit tl)
  end.

(* Controlled-V_j block: I + |j><j| (x) (V_j - I) for the j-th LCU term *)
Definition build_cntlV (lp : lowprog) (nqcn nqv idx : nat) : ucom ExtractionGateSet.U :=
  match nth_error lp idx with
  | None => ExtractionGateSet.SKIP
  | Some vi =>
      let nl      := cnt2bin idx nqcn in
      let control := cntl2pauli_helper nl in
      let vm1     := vi :: (Copp C1, fun _ => paulii) :: nil in
      let t2      := plus_ten_plus nqcn nqv control vm1 in
      LCU_digital_ibm (nqcn + nqv) ((C1, fun _ => paulii) :: t2)
  end.

(* One LCU segment: H^{(x)m} . SELECT . H^{(x)m}
   m = log2(#terms) control qubits; SELECT applies each controlled-V_j *)
Definition build_circuit_seg (nqv : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nterm    := length input in
  let nqcn     := Nat.log2_up nterm in
  let select   := fold_left ExtractionGateSet.useq
                    (map (build_cntlV input nqcn nqv) (seq 0 nterm))
                    ExtractionGateSet.SKIP in
  let hadamard := fold_left
                    (fun acc i => ExtractionGateSet.useq acc (ExtractionGateSet.H i))
                    (seq 0 nqcn) ExtractionGateSet.SKIP in
  ExtractionGateSet.useq (ExtractionGateSet.useq hadamard select) hadamard.


(* LCU Taylor series simulation of e^{-itH} to within error err.
   Splits [0,t] into r segments of length tau = t/r,
   builds Taylor LCU circuit for each segment, composes r copies. *)
Definition TTS_LCU (err t : R) (nbit : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in
  let tau      := (t / INR nseg)%R in
  let K        := findK_tau err nseg in
  let prog_seg := taylor_exp tau nbit K input in
  let circ_seg := build_circuit_seg nbit prog_seg in
  fold_left (fun acc _ => ExtractionGateSet.useq acc circ_seg)
    (seq 0 nseg) ExtractionGateSet.SKIP.
