(* QBlueTTS_opt.v — Taylor series LCU with PRX optimisations only *)
(* Babbush et al. PRX 8, 041015 (2018), Sections II B, III A, III C/D *)
From SQIR Require Import ExtractionGateSet.
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSynthDigital.
Require Import QBlue.QBlueQROM.
Require Import QBlue.QBluePEA.


(* Use "Lecture Notes on Quantum Algorithms" by Andrew M. Childs, Chapter 28.3
   and Babbush et al. PRX 8, 041015 (2018) Sections III A, III C/D, II B. *)


(* 1-norm of H: lambda = sum_j |alpha_j| *)
Definition ham_one_norm (lp : lowprog) : R :=
  fold_left (fun (acc : R) (x : lowprog_ten) => Rplus acc (Cmod (fst x))) lp 0%R.

(* Number of segments r = ceil(lambda * t / ln 2) *)
Definition get_nseg (t : R) (lp : lowprog) : nat :=
  let lambda := ham_one_norm lp in
  ceilR_N (lambda * t / ln 2).

(* Truncation order K: smallest k s.t. (ln2)^{k+1}/(k+1)! <= bound *)
Fixpoint findK_upto (fuel : nat) (bound aux : R) (k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Rltb aux bound || Reqb aux bound then k
      else findK_upto fuel' bound (aux * (ln 2) / INR (k + 2)) (S k)
  end.

Definition findK_tau (err : R) (r : nat) : nat :=
  let bound := (err / (4 * INR r))%R in
  findK_upto 64 bound (ln 2) 0.

(* Split complex amplitude (a + ib) * P into real terms for digital synthesis *)
Definition realify_lowprog_term (ten : lowprog_ten) : lowprog :=
  let (c, f) := ten in
  let re := fst c in
  let im := snd c in
  let real_part := if Reqb re R0 then nil else [(RtoC re, f)] in
  let imag_part := if Reqb im R0 then nil else [(Cmult Ci (R0, im), f)] in
  real_part ++ imag_part.

Fixpoint realify_lowprog (lp : lowprog) : lowprog :=
  match lp with
  | []      => []
  | t :: tl => realify_lowprog_term t ++ realify_lowprog tl
  end.

(* H^0 = I, H^k = H * H^{k-1} *)
Fixpoint cal_lowp_power (nqubit k : nat) (lp : lowprog) : lowprog :=
  match k with
  | 0    => [(C1, fun _ => paulii)]
  | S k' => plus_app_plus nqubit lp (cal_lowp_power nqubit k' lp)
  end.

(* k-th Taylor coefficient c_k = (-i)^k * t^k / k! *)
Definition taylor_coeff (t : R) (k : nat) : C :=
  Cmult (Cpow (Copp Ci) k) (RtoC (pow t k / INR (factor k))).

(* Truncated Taylor series sum_{k=0}^{K} c_k * H^k *)
Fixpoint taylor_exp (t : R) (nqubit K : nat) (lp : lowprog) : lowprog :=
  match K with
  | 0    => mult_ampli_hplus (taylor_coeff t 0) (cal_lowp_power nqubit 0 lp)
  | S k' =>
      let term_K := mult_ampli_hplus (taylor_coeff t K) (cal_lowp_power nqubit K lp) in
      term_K ++ taylor_exp t nqubit k' lp
  end.


(* Ancilla qubit layout above the nqcn index qubits and nqv system qubits:
     sel_root  = nqcn + nqv            SELECT tree root ancilla
     sel_pancs = nqcn + nqv + 1 ..     nqcn SELECT path ancillae
     qrom_out  = nqcn + nqv + nqcn + 1 amp_m QROM output qubits
     qrom_root = qrom_out + amp_m       QROM root ancilla
     qrom_pancs = qrom_root + 1 ..      nqcn QROM path ancillae *)
Definition tts_amp_m : nat := 20.

Definition tts_sel_root   (nqcn nqv : nat) : nat := nqcn + nqv.
Definition tts_sel_pancs  (nqcn nqv : nat) : list nat := seq (nqcn + nqv + 1) nqcn.
Definition tts_qrom_out   (nqcn nqv : nat) : nat := nqcn + nqv + nqcn + 1.
Definition tts_qrom_root  (nqcn nqv : nat) : nat := nqcn + nqv + nqcn + 1 + tts_amp_m.
Definition tts_qrom_pancs (nqcn nqv : nat) : list nat :=
  seq (nqcn + nqv + nqcn + 1 + tts_amp_m + 1) nqcn.

(* Leaf operation for unary iteration: apply V_idx to system qubits *)
Definition tts_leaf_op (lp : lowprog) (nqcn nqv idx : nat)
    : ucom ExtractionGateSet.U :=
  match nth_error lp idx with
  | None          => ExtractionGateSet.SKIP
  | Some (amp, f) => synth_digital_ibm_apauli (fst amp) (nqcn + nqv) f
  end.


(* Optimised LCU segment (Babbush et al. PRX 2018):
     PREPARE  = qrom_prepare    O(L) T gates  (Sec. III C/D)
     SELECT   = unary_iter_select O(L) T gates (Sec. III A)
     UNPREPARE = invert PREPARE *)
Definition build_circuit_seg_opt (nqv : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let input' := realify_lowprog input in
  let L      := length input' in
  let nqcn   := Nat.log2_up L in
  let amps   := lowprog_to_amps input' in
  let PREP   := qrom_prepare nqcn tts_amp_m 0
                  (tts_qrom_out nqcn nqv) (tts_qrom_root nqcn nqv)
                  (tts_qrom_pancs nqcn nqv) amps in
  let SELECT := unary_iter_select L nqcn 0
                  (tts_sel_root nqcn nqv) (tts_sel_pancs nqcn nqv)
                  (tts_leaf_op input' nqcn nqv) in
  ExtractionGateSet.useq PREP
    (ExtractionGateSet.useq SELECT (invert PREP)).


(* Optimised TTS time evolution: r segments, each using build_circuit_seg_opt *)
Definition TTS_LCU_opt (err t : R) (nbit : nat) (input : lowprog)
    : ucom ExtractionGateSet.U :=
  let nseg     := get_nseg t input in
  let tau      := (t / INR nseg)%R in
  let K        := findK_tau err nseg in
  let prog_seg := taylor_exp tau nbit K input in
  let circ_seg := build_circuit_seg_opt nbit prog_seg in
  fold_left (fun acc _ => ExtractionGateSet.useq acc circ_seg)
    (seq 0 nseg) ExtractionGateSet.SKIP.


(* Heisenberg-limited PEA for TTS (Babbush et al. Sec. II B).
   O(lambda/epsilon) query complexity vs O(lambda t) for direct simulation.
   m        : number of PEA control qubits
   pea_base : first PEA control qubit
   pea_anc  : ancilla for prepare_chi
   n_anc    : LCU ancilla register size
   refl_aux : scratch qubit for reflect_ancilla *)
Definition TTS_LCU_heis (err t : R) (nbit m pea_base pea_anc n_anc refl_aux : nat)
    (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg   := get_nseg t input in
  let tau    := (t / INR nseg)%R in
  let K      := findK_tau err nseg in
  let lp'    := realify_lowprog (taylor_exp tau nbit K input) in
  let L      := length lp' in
  let nqcn   := Nat.log2_up L in
  let amps   := lowprog_to_amps lp' in
  let PREP   := qrom_prepare nqcn tts_amp_m 0
                  (tts_qrom_out nqcn nbit) (tts_qrom_root nqcn nbit)
                  (tts_qrom_pancs nqcn nbit) amps in
  let SELECT := unary_iter_select L nqcn 0
                  (tts_sel_root nqcn nbit) (tts_sel_pancs nqcn nbit)
                  (tts_leaf_op lp' nqcn nbit) in
  heis_pea_from_lcu m pea_base pea_anc n_anc refl_aux PREP SELECT.