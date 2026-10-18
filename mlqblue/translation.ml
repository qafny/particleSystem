open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueSynth
open QBlueTrotter
open QBlueQdrift
open QBlueMarQSim
open QBlueCompile
open QBlueUtility
open ExtractionGateSet
open UnitaryListRepresentation
open Qblue_util

let marqsim_term_limit = 2000

(* Dispatch on the target connectivity chosen with -arch *)
let ibmdigi_voqc_optimize nq =
  if !target_a2a then ibmdigi_voqc_optimize_a2a nq else QBlueSynthDigital.ibmdigi_voqc_optimize nq
let ibmdigi_to_rzq nq =
  if !target_a2a then ibmdigi_to_rzq_a2a nq else QBlueSynthDigital.ibmdigi_to_rzq nq

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
  let r = trotter_step err t nbit (lowprog2norm_prog lp) in
  let nt = Stdlib.List.length lp in
  let totw = sum_w (lowprog2norm_prog lp) nt in
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
  let r = trotter_step err t nq (lowprog2norm_prog lp) in
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
	(cc, cir_bf, ts, r, npau)
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

(* LCU methods -> IBM digital circuits (QBlueQSVT.v, QBlueQubitization.v,
   QBlueTTS_v4.v, QBlueQuantumWalk.v). *_pieces describe a circuit as distinct pieces with multiplicities;
   each piece is compiled once (in chunks of lcu_chunk gates, 1000 by default,
   QBLUE_LCU_CHUNK to change) and its counts are multiplied. Returns
   (1q, CX, 1q before VOQC, CX before VOQC, time, total qubits, segments). *)
let lcu_chunk =
  try int_of_string (Sys.getenv "QBLUE_LCU_CHUNK") with Not_found | Failure _ -> 1000

let rec split_chunks acc cur n = function
  | [] -> List.rev (if cur = [] then acc else List.rev cur :: acc)
  | g :: rest ->
    if n = lcu_chunk then split_chunks (List.rev cur :: acc) [g] 1 rest
    else split_chunks acc (g :: cur) (n + 1) rest

let count_lcu_piece_uncached nq (piece : QBlueQuantumWalk.gl) =
  List.fold_left (fun (s1, s2, s3, s4) chunk ->
      let u = QBlueQuantumWalk.to_ucom chunk in
      let raw = ibmdigi_to_rzq nq u and opt = ibmdigi_voqc_optimize nq u in
      let cx_raw = voqc_count_CX nq raw and cx_opt = voqc_count_CX nq opt in
      (s1 + voqc_count_total nq opt - cx_opt, s2 + cx_opt,
       s3 + voqc_count_total nq raw - cx_raw, s4 + cx_raw))
    (0, 0, 0, 0) (split_chunks [] [] 0 piece)

(* The heavy pieces (SELECT, walk, block encoding) do not depend on the error
   bound or time, so with QBLUE_LCU_CACHE set their counts are stored on disk,
   keyed by the exact gates, qubit count, chunk size and target, and reused by
   the other jobs of the same program. *)
let count_lcu_piece nq (piece : QBlueQuantumWalk.gl) =
  match Sys.getenv_opt "QBLUE_LCU_CACHE" with
  | None | Some "" -> count_lcu_piece_uncached nq piece
  | Some dir ->
    let key = Digest.to_hex (Digest.string
        (Marshal.to_string (nq, lcu_chunk, !target_a2a, piece) [Marshal.No_sharing])) in
    let path = Filename.concat dir (key ^ ".counts") in
    (try
       let ic = open_in path in
       let r = Scanf.sscanf (input_line ic) "%d %d %d %d" (fun a b c d -> (a, b, c, d)) in
       close_in ic; r
     with _ ->
       let (a, b, c, d) as r = count_lcu_piece_uncached nq piece in
       (try
          if not (Sys.file_exists dir) then Sys.mkdir dir 0o755;
          let tmp = Filename.temp_file ~temp_dir:dir "counts" ".tmp" in
          let oc = open_out tmp in
          Printf.fprintf oc "%d %d %d %d\n" a b c d;
          close_out oc;
          Sys.rename tmp path
        with Sys_error _ -> ());
       r)

(* qubits a piece touches: 1 + its highest qubit index. Counting a piece on its
   own width keeps its cached counts independent of the method's total width. *)
let piece_width (piece : QBlueQuantumWalk.gl) =
  let open ExtractionGateSet in
  let rec go m = function
    | Coq_useq (a, b) -> go (go m a) b
    | Coq_uapp (_, _, qs) -> List.fold_left max m qs in
  1 + List.fold_left go 0 piece

let lcu_IBMDigital ?(verbose=false) name pieces (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- %s -> IBMDigital circuits: ----" name;
  let ts = Unix.gettimeofday () in
  let (((nq_total, segments), degree), parts) = pieces err t nq lp in
  let total = List.fold_left (fun (a, b, c, d) (mult, piece) ->
      let (p1, p2, p3, p4) = count_lcu_piece (piece_width piece) piece in
      (a + mult * p1, b + mult * p2, c + mult * p3, d + mult * p4)) (0, 0, 0, 0) parts in
  let (n1, n2, n3, n4) = total in
  if verbose then
    dbg "%s: %d qubits, %d segment(s), degree/order %d -> 1Q=%d CX=%d (before VOQC 1Q=%d CX=%d)"
      name nq_total segments degree n1 n2 n3 n4;
  (n1, n2, n3, n4, Unix.gettimeofday () -. ts, nq_total, segments)

let lcu_path_name = function
  | 8 -> "QSVT" | 9 -> "QSP (generalized QSP on the qubitization walk)"
  | 30 -> "Taylor series LCU" | 31 -> "Quantum walk (qubitization + Jacobi-Anger LCU)"
  | p -> failwith (Printf.sprintf "path %d is not an LCU method" p)

let lcu_pieces = function
  | 8 -> QBlueQSVT.qsvt_pieces | 9 -> QBlueQubitization.qsp_pieces
  | 30 -> QBlueTTS_v4.taylor_pieces | 31 -> QBlueQuantumWalk.qwalk_pieces
  | p -> failwith (Printf.sprintf "path %d is not an LCU method" p)

let is_lcu_path p = List.mem p [8; 9; 30; 31]

let lcu_counts ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) (path : int) =
  lcu_IBMDigital ~verbose (lcu_path_name path) (lcu_pieces path) lp nq err t

(* 2nd-order trotterization; decompose to IBM digital *)
let trotter2nd_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) = 
  if verbose then dbg "---- Trotterization (2nd-order) -> IBMDigital circuits: ----";
  let r = trotter_step_2nd_order err t nq (lowprog2norm_prog lp) in
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
    in (cc, cir_bf, ts, r, npau) 
  
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterQDrift_IBMDigi_est (lp : lowprog) (nbit : int) (err : float) (t : float) f_opt =
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let totw = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in
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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
    (cc, cir_bf, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterQDrift_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterMarQSim_CNOT_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT matrix) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT matrix) -> IBMDigital" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (transition_mat, ts1) = time_call (fun () -> get_trans_CNOT lp nq) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 in
    (cc, cir_bf, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQSim_CNOT_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_mix_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT + single-qubit matrix) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT + single-qubit matrix) -> IBMDigital" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (transition_mat, ts1) = time_call (fun () -> get_trans_mixed lp nq) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 in
    (cc, cir_bf, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQSim_mix_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterMarQdrift_CNOT_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, 0.6 * CNOT + 0.4 * qdrift) -> IBMDigital circuits: ----";
  fail_big_program "MarQSim (CNOT + qdrift) -> IBMDigital" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (f_mat, ts1) = time_call (fun () -> get_trans_CNOT lp nq) in
	 let (transition_mat, ts3) = time_call (fun () -> get_trans_MarQdrift lp 0.6 f_mat) in
    
	let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 +. ts3 in
    (cc, cir_bf, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQdrift_CNOT_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_mix_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQdrift, 0.6 * CNOT + single-qubit + 0.4 * qdrift) -> IBMDigital circuits: ----";
  fail_big_program "MarQdrift ( CNOT + single-qubit + qdrift) -> IBMDigital" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
	let (f_mat, ts1) = time_call (fun () -> get_trans_mixed lp nq) in
	let (transition_mat, ts3) = time_call (fun () -> get_trans_MarQdrift lp 0.6 f_mat) in
    let cir_bf = translate_lowp2circ_marqsim err t lp nq (ibmdigi_to_rzq nq) transition_mat in
    let cc, ts2 = time_call (fun () -> translate_lowp2circ_marqsim err t lp nq (ibmdigi_voqc_optimize nq) transition_mat) in
    let ts = ts1 +. ts2 +. ts3 in
    (cc, cir_bf, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQdrift_mix_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn



(* std trotterization; decompose to Indiana Analog *)
let trotterStd_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> Indiana analog circuits: ----";
  let r = trotter_step err t nq (lowprog2norm_prog lp) in
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
  let r = trotter_step_2nd_order err t nq (lowprog2norm_prog lp) in
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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_qdrift err t lp nq) in
    (cc, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterQDrift_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_CNOT_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT matrix) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT matrix) -> IndiAnalog" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let transition_mat = get_trans_CNOT lp nq in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQSim_CNOT_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQSim_mix_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, CNOT + single-qubit matrix) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT + single-qubit matrix) -> IndiAnalog" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let transition_mat = get_trans_mixed lp nq in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQSim_mix_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_CNOT_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim, 0.6 * CNOT + 0.4 * qdrift) -> IndiAnalog circuits: ----";
  fail_big_program "MarQSim (CNOT + qdrift) -> IndiAnalog" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let f_mat = get_trans_CNOT lp nq in
    let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQdrift_CNOT_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterMarQdrift_mix_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQdrift, 0.6 * CNOT + single-qubit + 0.4 * qdrift) -> IndiAnalog circuits: ----";
  fail_big_program "MarQdrift (CNOT + single-qubit + qdrift) -> IndiAnalog" lp;
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let f_mat = get_trans_mixed lp nq in
    let transition_mat = get_trans_MarQdrift lp 0.6 f_mat in
    let cc, ts = time_call (fun () -> translate_lowp2IndiAna_marqsim err t lp nq transition_mat) in
    (cc, ts, sample_repeats npau, npau)
  with exn -> dbg "trotterMarQdrift_mix_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn


(* std trotterization; decompose to IBM Analog *)
let trotterStd_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> IBM analog circuits: ----";
  let r = trotter_step err t nq (lowprog2norm_prog lp) in
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
  let r = trotter_step_2nd_order err t nq (lowprog2norm_prog lp) in
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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
  let npau = qdrift_step err t (lowprog2norm_prog lp) in
  let lambda = sum_w (lowprog2norm_prog lp) (Stdlib.List.length lp) in

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
