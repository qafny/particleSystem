open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueSynth
open QBlueTrotter
open QBlueQdrift
open QBlueCompile
open ExtractionGateSet
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

    let cir_bf =
      translate_lowp2circ_2ndTrotter err t lp nq (ibmdigi_to_rzq nq)
    in
    let cc, ts =
      time_call (fun () -> translate_lowp2circ_2ndTrotter err t lp nq (ibmdigi_voqc_optimize nq))
    in
    (cc, cir_bf, ts, r) 
  
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

let trotterMarQSim_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim -> IBMDigital" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cir_bf =
      translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq)
    in
    let cc, ts =
      time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq))
    in
    (cc, cir_bf, ts, 1)
  with exn -> dbg "trotterMarQSim_IBMDigital raise EXN: %s" (Printexc.to_string exn);
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

let trotterMarQSim_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim -> IndiAnalog" lp;
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq) in
    (cc, ts, 1, npau)
  with exn -> dbg "trotterMarQSim_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn
