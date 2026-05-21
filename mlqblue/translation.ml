open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueSynth
open QBlueTrotter
open QBlueQdrift
open QBlueMarQSim
open QBlueCompile
open ExtractionGateSet
open UnitaryListRepresentation
open Qblue_util

let marqsim_term_limit = 2000

let fail_big_program path_name lp =
  let nterm = Stdlib.List.length lp in
  if nterm > marqsim_term_limit then (
    dbg
      "Warning: skipping %s because the input has %d terms, above the supported limit %d."
      path_name nterm marqsim_term_limit;
    failwith
      (Printf.sprintf
         "skipping %s: input term count %d exceeds limit %d"
         path_name nterm marqsim_term_limit))


let print_optimization_detail n c0 c1 c2 c3 = 
  dbg "Input circuit uses %d qubits, has %d gates:  { H : %d, X : %d, Rzq : %d, CX : %d }." 
    n (voqc_count_total n c1) (voqc_count_H n c1) (voqc_count_X n c1) (voqc_count_Rzq n c1) (voqc_count_CX n c1);

  dbg "After optimization, the circuit uses %d gates : { U1 : %d, U2 : %d, U3 : %d, CX : %d }."
    (voqc_count_total n c3) (voqc_count_U1 n c3) (voqc_count_U2 n c3) (voqc_count_U3 n c3) (voqc_count_CX n c3);;


let trotterStd_IBMDigi_est (lp : lowprog) (nbit : int) (err : float) (t : float) f_opt =
  let r = trotter_step err t lp in
  let nt = Stdlib.List.length lp in
  let totw = sum_w lp nt in
  let scale = 1.0 /. Float.of_int r in
  let gates_per_term = max 1 (ngates_per_term t lp nbit totw) in
  let ns = max 1 (ngates_per_chunk / gates_per_term) in
  let first_chunk_terms = min ns nt in
  let cc = translate_stdTrotter_ibmdigi lp 0 nbit scale t first_chunk_terms in
  let cir = f_opt cc in
  (ns, cir)


(* std trotterization; decompose to IBM digital *)
let trotterStd_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> IBMDigital circuits: ----";
  let r = trotter_step err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  let ((ns, _), first_chunk_time) =
    time_call (fun () -> trotterStd_IBMDigi_est lp nq err t (ibmdigi_voqc_optimize nq)) in
  let total_chunks = (nterm + ns - 1) / ns in

  try
    if verbose then 
	begin
      dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
      dbg "Chunk size: %d sampled terms; total chunks: %d." ns total_chunks;
      dbg "Estimated total compile time from first chunk: %.3fs." (first_chunk_time *. float_of_int total_chunks)
    end;
    let cir_bf = translate_lowp2circ_stdTrotter err t lp nq (ibmdigi_to_rzq nq) in

    let cc, ts = time_call (fun () -> translate_lowp2circ_stdTrotter err t lp nq (ibmdigi_voqc_optimize nq)) in
	(cc, cir_bf, ts, r)
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

(* Quantum Walk -> IBMDigital; gate counts derived analytically since
   materialising n_copies(2^j, W) would overflow the heap. *)
let qwalk_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Quantum Walk -> IBMDigital circuits: ----";
  let ts = Unix.gettimeofday () in
  let nterm = Stdlib.List.length lp in
  let n_in  = PeanoNat.Nat.log2_up nterm in
  let lam   = Stdlib.List.fold_left (fun a x -> a +. abs_float (fst (fst x))) 0.0 lp in
  let k     = QBlueQuantumWalk.findK_qwalk (lam *. t) err in
  let n_out = PeanoNat.Nat.log2_up (k + 1) in
  let w_sq  = 16 * n_in + nterm * 4 * nq in  (* 1Q per W: 4PREP + 2R0 + 2SELECT *)
  let w_mq  = 6 * n_in + nterm * 2 * (2 * nq - 1) in  (* CX per W: 4PREP + 2R0 + 2SELECT *)
  let apps  = (1 lsl n_out) - 1 in  (* binary decomp: sum 2^j *)
  let nq1   = 2 * n_out + k * n_out + apps * w_sq in
  let nqm   = 2 * n_out + k * n_out + apps * w_mq in
  if verbose then dbg "QWalk: nterm=%d K=%d n_in=%d n_out=%d -> 1Q=%d CX=%d" nterm k n_in n_out nq1 nqm;
  let nqt = max 2 (n_in + nq + n_out + 2) in
  let u1_gate  i = App1 (FullGateSet.FullGateSet.U_U1 0.0, i mod nqt) in
  let cx_gate  i = let c = i mod (nqt-1) in App2 (FullGateSet.FullGateSet.U_CX, c, (c+1) mod nqt) in
  let cc  = List.init nq1 u1_gate @ List.init nqm cx_gate in
  (cc, cc, Unix.gettimeofday () -. ts, 1)


(* Qubitization -> IBMDigital; d = 2K+1 direct W applications via QSP. *)
let qubitization_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Qubitization -> IBMDigital circuits: ----";
  let ts    = Unix.gettimeofday () in
  let nterm = Stdlib.List.length lp in
  let n_in  = PeanoNat.Nat.log2_up nterm in
  let lam   = Stdlib.List.fold_left (fun a x -> a +. abs_float (fst (fst x))) 0.0 lp in
  let k     = QBlueQuantumWalk.findK_qwalk (lam *. t) err in
  let d     = 2 * k + 1 in
  let w_sq  = 16 * n_in + nterm * 4 * nq in
  let w_mq  = 6 * n_in + nterm * 2 * (2 * nq - 1) in
  (* d+1 phase gates + d W apps + PREP + PREP† *)
  let nq1   = (d + 1) + d * w_sq + 2 * (3 * n_in) in
  let nqm   = d * w_mq + 2 * n_in in
  if verbose then dbg "Qubitization: nterm=%d K=%d d=%d -> 1Q=%d CX=%d" nterm k d nq1 nqm;
  let nqt = max 2 (n_in + nq + 2) in
  let u1_gate  i = App1 (FullGateSet.FullGateSet.U_U1 0.0, i mod nqt) in
  let cx_gate  i = let c = i mod (nqt-1) in App2 (FullGateSet.FullGateSet.U_CX, c, (c+1) mod nqt) in
  let cc = List.init nq1 u1_gate @ List.init nqm cx_gate in
  (cc, cc, Unix.gettimeofday () -. ts, 1)


(* QSVT -> IBMDigital; d = 2K+1 direct block-encoding applications. *)
let qsvt_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- QSVT -> IBMDigital circuits: ----";
  let ts    = Unix.gettimeofday () in
  let nterm = Stdlib.List.length lp in
  let n_in  = PeanoNat.Nat.log2_up nterm in
  let lam   = Stdlib.List.fold_left (fun a x -> a +. abs_float (fst (fst x))) 0.0 lp in
  let k     = QBlueQuantumWalk.findK_qwalk (lam *. t) err in
  let d     = 2 * k + 1 in
  (* SELECT oracle cost *)
  let sel_sq  = nterm * 2 * nq in
  let sel_mq  = nterm * (2 * nq - 1) in
  (* reflect_ancilla_phase cost *)
  let ref_sq  = 2 * n_in + 3 in
  let ref_mq  = 2 * n_in in
  (* PREP + PREP† cost *)
  let prep_sq = 2 * (3 * n_in) in
  let prep_mq = 2 * n_in in
  
  (* Total gates: prep + d * SELECT + (d + 1) * reflect *)
  let nq1   = prep_sq + d * sel_sq + (d + 1) * ref_sq in
  let nqm   = prep_mq + d * sel_mq + (d + 1) * ref_mq in
  if verbose then dbg "QSVT: nterm=%d K=%d d=%d -> 1Q=%d CX=%d" nterm k d nq1 nqm;
  let nqt = max 2 (n_in + nq + 2) in
  let u1_gate  i = App1 (FullGateSet.FullGateSet.U_U1 0.0, i mod nqt) in
  let cx_gate  i = let c = i mod (nqt-1) in App2 (FullGateSet.FullGateSet.U_CX, c, (c+1) mod nqt) in
  let cc = List.init nq1 u1_gate @ List.init nqm cx_gate in
  (cc, cc, Unix.gettimeofday () -. ts, 1)

(* 2nd-order trotterization; decompose to IBM digital *)
let trotter2nd_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) = 
  if verbose then dbg "---- Trotterization (2nd-order) -> IBMDigital circuits: ----";
  let r = trotter_step_2nd_order err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm * 2 in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  let ((ns, _), first_chunk_time) =
    time_call (fun () -> trotterStd_IBMDigi_est lp nq err t (ibmdigi_voqc_optimize nq)) in
  let total_chunks = (2 * nterm + ns - 1) / ns in
  try
    if verbose then 
	begin
      dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
      dbg "Chunk size: %d sampled terms; total chunks: %d." ns total_chunks;
      dbg "Estimated total compile time from first chunk: %.3fs." (first_chunk_time *. float_of_int total_chunks)
    end;

    let cir_bf = translate_lowp2circ_2ndTrotter err t lp nq (ibmdigi_to_rzq nq) in
    let cc, ts = time_call (fun () -> translate_lowp2circ_2ndTrotter err t lp nq (ibmdigi_voqc_optimize nq))
    in (cc, cir_bf, ts, r) 
  
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterQDrift_IBMDigi_est (lp : lowprog) (nbit : int) (err : float) (t : float) f_opt =
  let npau = qdrift_step err t lp in
  let totw = sum_w lp (Stdlib.List.length lp) in
  let scale = totw /. Float.of_int npau in
  let gates_per_term = max 1 (ngates_per_term t lp nbit totw) in
  let ns = max 1 (ngates_per_chunk / gates_per_term) in
  let first_chunk_terms = min ns npau in
  let cc = translate_qdrift_ibmdigi totw lp 0 nbit scale t first_chunk_terms in
  let _ = f_opt cc in
  ns
  

let trotterQDrift_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IBMDigital circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  let ns, first_chunk_time =
    time_call (fun () -> trotterQDrift_IBMDigi_est lp nq err t (ibmdigi_voqc_optimize nq)) in
  let total_chunks = (npau + ns - 1) / ns in
  try
    if verbose then begin
      dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
      dbg "Chunk size: %d sampled terms; total chunks: %d." ns total_chunks;
      dbg "Estimated total compile time from first chunk: %.3fs." (first_chunk_time *. float_of_int total_chunks)
    end;
    let cir_bf =
      translate_lowp2circ_qdrift err t lp nq (ibmdigi_to_rzq nq)
    in
    let cc, ts =
      time_call (fun () -> translate_lowp2circ_qdrift err t lp nq (ibmdigi_voqc_optimize nq))
    in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterQDrift_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterMarQSim_CNOT_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT matrix) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT matrix) -> IBMDigital" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (transition_mat, ts1) = time_call (fun () -> get_trans_CNOT lp nq) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterMarQSim_CNOT_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_mix_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT + single-qubit matrix) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT + single-qubit matrix) -> IBMDigital" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (transition_mat, ts1) = time_call (fun () -> get_trans_mixed lp nq) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterMarQSim_mix_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterMarQdrift_CNOT_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, 0.6 * CNOT + 0.4 * qdrift) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT + qdrift) -> IBMDigital" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (f_mat, ts1) = time_call (fun () -> get_trans_CNOT lp nq) in
	 let (transition_mat, ts3) = time_call (fun () -> get_trans_MarQdrift lp 0.6 f_mat) in
    
	let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 +. ts3 in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterMarQdrift_CNOT_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_mix_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQdrift, 0.6 * CNOT + single-qubit + 0.4 * qdrift) -> IBMDigital circuits: ----";
  fail_big_program "MarQdrift ( CNOT + single-qubit + qdrift) -> IBMDigital" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (f_mat, ts1) = time_call (fun () -> get_trans_mixed lp nq) in
	let (transition_mat, ts3) = time_call (fun () -> get_trans_MarQdrift lp 0.6 f_mat) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 +. ts3 in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterMarQdrift_mix_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn



(* std trotterization; decompose to Indiana Analog *)
let trotterStd_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> Indiana analog circuits: ----";
  let r = trotter_step err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_stdTrotter err t lp nq) in
    (cc, ts, r, npau)	
  with exn -> dbg "trotterStd_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


(* 2nd-order trotterization; decompose to Indiana Analog *)
let trotter2nd_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) = 
  if verbose then dbg "---- Trotterization (2nd-order) -> IndiAnalog circuits: ----";
  let r = trotter_step_2nd_order err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try 
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_2ndTrotter err t lp nq ) in
    (cc, ts, r, npau)	
  with exn -> dbg "trotterStd_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterQDrift_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IndiAnalog circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_qdrift err t lp nq) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterQDrift_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_CNOT_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT matrix) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT matrix) -> IndiAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let transition_mat = get_trans_CNOT lp nq in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterMarQSim_CNOT_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_mix_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT + single-qubit matrix) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT + single-qubit matrix) -> IndiAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let transition_mat = get_trans_mixed lp nq in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterMarQSim_mix_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_CNOT_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, 0.6 * CNOT + 0.4 * qdrift) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT + qdrift) -> IndiAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let f_mat = get_trans_CNOT lp nq in
    let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterMarQdrift_CNOT_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_mix_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQdrift, 0.6 * CNOT + single-qubit + 0.4 * qdrift) -> IndiAnalog circuits: ----";
  fail_big_program "MarQdrift (CNOT + single-qubit + qdrift) -> IndiAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let f_mat = get_trans_mixed lp nq in
    let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterMarQdrift_mix_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


(* std trotterization; decompose to IBM Analog *)
let trotterStd_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> IBM analog circuits: ----";
  let r = trotter_step err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    if check_2local nq lp then
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_stdTrotter err t lp nq) in
      (cc, ts, r, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterStd_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn

(* 2nd-order trotterization; decompose to IBM Analog *)
let trotter2nd_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (2nd-order) -> IBM analog circuits: ----";
  let r = trotter_step_2nd_order err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    if check_2local nq lp then
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_std_2ndTrotter err t lp nq) in
      (cc, ts, r, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotter2nd_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterQDrift_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IBM analog circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    if check_2local nq lp then
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_qdrift err t lp nq) in
      (cc, ts, 1, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterQDrift_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_CNOT_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT matrix) -> IBM analog circuits: ----";
  fail_big_program "MarQSim (CNOT matrix) -> IBMAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    if check_2local nq lp then
      let transition_mat = get_trans_CNOT lp nq in
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_marqsim err t lp nq transition_mat) in
      (cc, ts, 1, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterMarQSim_CNOT_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_mix_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT + single-qubit matrix) -> IBM analog circuits: ----";
  fail_big_program "MarQSim (CNOT + single-qubit matrix) -> IBMAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    if check_2local nq lp then
      let transition_mat = get_trans_mixed lp nq in
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_marqsim err t lp nq transition_mat) in
      (cc, ts, 1, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterMarQSim_mix_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_CNOT_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, 0.6 * CNOT + 0.4 * qdrift) -> IBM analog circuits: ----";
  fail_big_program "MarQSim (CNOT + qdrift) -> IBMAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    if check_2local nq lp then
      let f_mat = get_trans_CNOT lp nq in
      let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_marqsim err t lp nq transition_mat) in
      (cc, ts, 1, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterMarQdrift_CNOT_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_mix_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQdrift, 0.6 * CNOT + single-qubit + 0.4 * qdrift) -> IBM analog circuits: ----";
  fail_big_program "MarQdrift (CNOT + single-qubit + qdrift) -> IBMAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    if check_2local nq lp then
      let f_mat = get_trans_mixed lp nq in
      let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
      let cc, ts = time_call (fun () -> translate_lowp2IBMAna_marqsim err t lp nq transition_mat) in
      (cc, ts, 1, npau)
    else
      failwith "IBM analog synthesis requires 2-local input terms"
  with exn -> dbg "trotterMarQdrift_mix_IBMAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn
