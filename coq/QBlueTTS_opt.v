(* Define the Taylor series simulation and LCU (Linear Combination of Unitaries) *)
From SQIR Require Import ExtractionGateSet.
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
      if Rltb aux bound || Reqb aux bound then k
      else findK_upto fuel' bound (aux * (ln 2) / INR (k + 2)) (S k)
  end.

(* r segments, per-segment bound = err / (4 * r) from Childs eq. (28.11)
   since e^{lambda*tau} <= e^{ln2} = 2, giving factor of 4 in denominator *)
Definition findK_tau (err : R) (r : nat) : nat :=
  let bound := (err / (4 * INR r))%R in
  findK_upto 64 bound (ln 2) 0.

(* Split (a + ib) * P into a*P + b*(i*P) with real coefficients for digital synth.
   Ci * (0, im) = (-im, 0) so the imaginary part becomes a real amplitude. *)
Definition realify_lowprog_term (ten : lowprog_ten) : lowprog :=
  let (c, f) := ten in
  let re := fst c in
  let im := snd c in
  let real_part :=
    if Reqb re R0 then nil else [(RtoC re, f)] in
  let imag_part :=
    if Reqb im R0 then nil else [(Cmult Ci (R0, im), f)] in
  real_part ++ imag_part.

Fixpoint realify_lowprog (lp : lowprog) : lowprog :=
  match lp with
  | [] => []
  | t :: tl => realify_lowprog_term t ++ realify_lowprog tl
  end.


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
      LCU_digital_ibm (nqcn + nqv)
        (realify_lowprog ((C1, fun _ => paulii) :: t2))
  end.

(* Per-segment Taylor lowprog (time step tau, truncation K). *)
Definition tts_segment_taylor (err t : R) (nbit : nat) (input : lowprog) : lowprog :=
  let nseg := get_nseg t input in
  let tau := (t / INR nseg)%R in
  let K := findK_tau err nseg in
  taylor_exp tau nbit K input.

(* Taylor lowprog for analog synthesis (coefficients already include tau). *)
Definition tts_analog_lowprog (err t : R) (nbit : nat) (input : lowprog) : lowprog :=
  realify_lowprog (tts_segment_taylor err t nbit input).

(* One LCU segment: H^{(x)m} . SELECT . H^{(x)m}
   m = log2(#terms) control qubits; SELECT applies each controlled-V_j *)
Definition build_circuit_seg (nqv : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let input' := realify_lowprog input in
  let nterm    := length input' in
  let nqcn     := Nat.log2_up nterm in
  let select   := fold_left ExtractionGateSet.useq
                    (map (build_cntlV input' nqcn nqv) (seq 0 nterm))
                    ExtractionGateSet.SKIP in
  let hadamard := fold_left
                    (fun acc i => ExtractionGateSet.useq acc (ExtractionGateSet.H i))
                    (seq 0 nqcn) ExtractionGateSet.SKIP in
  ExtractionGateSet.useq (ExtractionGateSet.useq hadamard select) hadamard.


(* LCU Taylor series simulation of e^{-itH} to within error err.
   Splits [0,t] into r segments of length tau = t/r,
   builds Taylor LCU circuit for each segment, composes r copies. *)
Definition TTS_LCU1 (err t : R) (nbit : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in
  let tau      := (t / INR nseg)%R in
  let K        := findK_tau err nseg in
  let prog_seg := taylor_exp tau nbit K input in
  let circ_seg := build_circuit_seg nbit prog_seg in
  fold_left (fun acc _ => ExtractionGateSet.useq acc circ_seg)
    (seq 0 nseg) ExtractionGateSet.SKIP.


(* ------------------------------------------------------------------ *)
(* ADDED: optimisations from Babbush et al. PRX 8, 041015 (2018).     *)
(* Requires QBlue.QBlueQROM and QBlue.QBluePEA to be compiled first. *)
(* ------------------------------------------------------------------ *)
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.

(* ADDED: ancilla qubit layout for the optimised segment circuit.
   Above the nqcn index qubits and nqv system qubits we allocate:
     sel_root_q  = nqcn + nqv          (SELECT tree root ancilla)
     sel_pancs   = nqcn + nqv + 1 ..   (nqcn SELECT tree path ancillae)
     qrom_out    = nqcn + nqv + nqcn + 1 .. (amp_m QROM output qubits)
     qrom_root_q = nqcn + nqv + nqcn + 1 + amp_m
     qrom_pancs  = qrom_root_q + 1 ..  (nqcn QROM path ancillae) *)
Definition tts_amp_m : nat := 20.

Definition tts_sel_root  (nqcn nqv : nat) : nat := nqcn + nqv.
Definition tts_sel_pancs (nqcn nqv : nat) : list nat :=
  seq (nqcn + nqv + 1) nqcn.
Definition tts_qrom_out  (nqcn nqv : nat) : nat :=
  nqcn + nqv + nqcn + 1.
Definition tts_qrom_root (nqcn nqv : nat) : nat :=
  nqcn + nqv + nqcn + 1 + tts_amp_m.
Definition tts_qrom_pancs (nqcn nqv : nat) : list nat :=
  seq (nqcn + nqv + nqcn + 1 + tts_amp_m + 1) nqcn.

(* ADDED: operation applied at each leaf of the unary iteration tree.
   Applies V_idx (a Pauli rotation) to system qubits nqcn..nqcn+nqv-1,
   singly controlled on the tree leaf indicator (handled by dfs_select). *)
Definition tts_leaf_op (lp : lowprog) (nqcn nqv idx : nat)
    : ucom ExtractionGateSet.U :=
  match nth_error lp idx with
  | None        => ExtractionGateSet.SKIP
  | Some (amp, f) =>
      synth_digital_ibm_apauli (fst amp) (nqcn + nqv) f
  end.

(* ADDED: optimised LCU segment using:
     PREPARE  = qrom_prepare (O(L) T gates, Babbush et al. Sec. III C/D)
     SELECT   = unary_iter_select (O(L) T gates, Babbush et al. Sec. III A)
     UNPREPARE = invert PREPARE
   Replaces build_circuit_seg which uses uniform Hadamard PREPARE (O(1) T)
   and multi-controlled SELECT (O(L log L) T). *)
Definition build_circuit_seg_opt (nqv : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let input'   := realify_lowprog input in
  let L        := length input' in
  let nqcn     := Nat.log2_up L in
  let amps     := lowprog_to_amps input' in
  let PREP     := qrom_prepare nqcn tts_amp_m 0
                    (tts_qrom_out nqcn nqv)
                    (tts_qrom_root nqcn nqv)
                    (tts_qrom_pancs nqcn nqv)
                    amps in
  let SELECT   := unary_iter_select L nqcn 0
                    (tts_sel_root nqcn nqv)
                    (tts_sel_pancs nqcn nqv)
                    (tts_leaf_op input' nqcn nqv) in
  let UNPREP   := invert PREP in
  ExtractionGateSet.useq PREP (ExtractionGateSet.useq SELECT UNPREP).

(* ADDED: optimised TTS_LCU using build_circuit_seg_opt.
   Same interface as TTS_LCU1; drop-in replacement. *)
Definition TTS_LCU_opt (err t : R) (nbit : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in
  let tau      := (t / INR nseg)%R in
  let K        := findK_tau err nseg in
  let prog_seg := taylor_exp tau nbit K input in
  let circ_seg := build_circuit_seg_opt nbit prog_seg in
  fold_left (fun acc _ => ExtractionGateSet.useq acc circ_seg)
    (seq 0 nseg) ExtractionGateSet.SKIP.

(* ADDED: Heisenberg-limited PEA wrapper for TTS (Babbush et al. Sec. II B).
   Performs QPE on the walk operator W built from one TTS segment PREP and SELECT,
   achieving O(lambda/epsilon) query complexity instead of O(lambda t) for TTS_LCU1.
   m         : number of PEA control qubits
   pea_base  : first PEA control qubit index
   pea_anc   : ancilla qubit for prepare_chi
   n_anc     : number of ancilla qubits in the LCU register
   refl_aux  : scratch qubit for reflect_ancilla in walk_operator *)
Definition TTS_LCU_heis (err t : R) (nbit m pea_base pea_anc n_anc refl_aux : nat)
    (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in
  let tau      := (t / INR nseg)%R in
  let K        := findK_tau err nseg in
  let prog_seg := taylor_exp tau nbit K input in
  let input'   := realify_lowprog prog_seg in
  let L        := length input' in
  let nqcn     := Nat.log2_up L in
  let amps     := lowprog_to_amps input' in
  let PREP     := qrom_prepare nqcn tts_amp_m 0
                    (tts_qrom_out nqcn nbit)
                    (tts_qrom_root nqcn nbit)
                    (tts_qrom_pancs nqcn nbit)
                    amps in
  let SELECT   := unary_iter_select L nqcn 0
                    (tts_sel_root nqcn nbit)
                    (tts_sel_pancs nqcn nbit)
                    (tts_leaf_op input' nqcn nbit) in
  heis_pea_from_lcu m pea_base pea_anc n_anc refl_aux PREP SELECT.