open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueTrotter
open QBlueQdrift
open QBlueCompile
open ExtractionGateSet
open Ab_group
open Ab_trotter
open Qblue_util


let print_optimization_detail n c0 c1 c2 c3 = 
  dbg "Input circuit uses %d qubits, has %d gates:  { H : %d, X : %d, Rzq : %d, CX : %d }." 
    n (voqc_count_total n c1) (voqc_count_H n c1) (voqc_count_X n c1) (voqc_count_Rzq n c1) (voqc_count_CX n c1);

  dbg "After optimization, the circuit uses %d gates : { U1 : %d, U2 : %d, U3 : %d, CX : %d }."
    (voqc_count_total n c3) (voqc_count_U1 n c3) (voqc_count_U2 n c3) (voqc_count_U3 n c3) (voqc_count_CX n c3);;



(* Use VOQC to optimize IBM Digital gate count *)
let ibmdigi_voqc_optimize ?(verbose=false) nqubit circ =
  let n = nqubit in
  (* Convert to the RzQ gate set and print more statistics *)
  prerr_endline "decompose to voqc";
  flush stderr;
  let cc = decompose_to_voqc_gates circ in
	  
  prerr_endline "convert to full gate set";
  flush stderr;
  let c0 = cvt_egate_fullgate n cc in

  prerr_endline "convert to rzq";
  flush stderr;

  let c1 = voqc_convert_to_rzq n c0 in

  (* Map to the 5 qubit LNN ring architecture *)
  let cg = voqc_make_lnn_ring 5 in
  let la = voqc_trivial_layout 5 in
  let c2 = voqc_decompose_swaps n (voqc_swap_route n c1 la cg (voqc_lnn_ring_path_finding_fun 5)) cg in

  (* Optimize again *)
  let c3 = voqc_optimize n c2 in
  if verbose then print_optimization_detail n c0 c1 c2 c3;
  c3;;



(* std trotterization; decompose to IBM digital *)
let trotterStd_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> IBMDigital circuits: ----";
  let r = trotter_step err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    let n = trotter_step err t lp in
    let astep = trotter_astep (Float.of_int n) lp in
    let cc = synth_digital_ibm t nq astep in	
    (ibmdigi_voqc_optimize ~verbose:verbose nq cc, n)	
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


(* 2nd-order trotterization; decompose to IBM digital *)
let trotter2nd_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) = 
  if verbose then dbg "---- Trotterization (2nd-order) -> IBMDigital circuits: ----";
  let r = trotter_step_2nd_order err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    let n = trotter_step_2nd_order err t lp in
    let astep1 = trotter_astep (( /. ) (Float.of_int n) 2.0) (Stdlib.List.rev lp) in
    let astep2 = trotter_astep (( /. ) (Float.of_int n) 2.0) lp in
    let astep = Stdlib.List.append astep1 astep2 in
    let cc = synth_digital_ibm t nq astep in	
    (ibmdigi_voqc_optimize ~verbose:verbose nq cc, n)	
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let trotterQDrift_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IBMDigital circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc = translate_lowp2circ_qdrift err t lp nq in
    (ibmdigi_voqc_optimize ~verbose:verbose nq cc, 1) 
  with exn -> dbg "trotterQDrift_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterMarQSim_IBMDigital ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim) -> IBMDigital circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc = translate_lowp2circ_marqsim err t lp nq in
    (ibmdigi_voqc_optimize ~verbose:verbose nq cc, 1)
  with exn -> dbg "trotterMarQSim_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let analog_backend_unavailable () =
  failwith
    "Indiana analog backend unavailable: missing extracted module QBlueSynth in mlqblue/qbluelib"


(* std trotterization; decompose to Indiana Analog *)
let trotterStd_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  if verbose then dbg "---- Trotterization (1st-order) -> Indiana analog circuits: ----";
  let _ = (lp, nq, err, t) in
  analog_backend_unavailable ()


(* 2nd-order trotterization; decompose to Indiana Analog *)
let trotter2nd_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) = 
  if verbose then dbg "---- Trotterization (2nd-order) -> IndiAnalog circuits: ----";
  let _ = (lp, nq, err, t) in
  analog_backend_unavailable ()


let trotterQDrift_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IndiAnalog circuits: ----";
  let _ = (lp, nq, err, t) in
  analog_backend_unavailable ()

let trotterMarQSim_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (MarQSim) -> IndiAnalog circuits: ----";

  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    let cc = translate_lowp2Indiana_marqsim err t lp nq in (cc, 1, npau)
  with exn -> dbg "trotterMarQSim_IndiAnalog raise EXN: %s" (Printexc.to_string exn);
    raise exn
