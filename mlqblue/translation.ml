open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueTrotter
open QBlueQdrift
open QBlueCompile
open Util
open Ab_group
open Ab_trotter


(* std trotterization; decompose to IBM digital *)
let trotterStd_IBMDigital ?(verbose=false) (err : float) (t : float) (lp : lowprog) (nq : int) =
  if verbose then dbg "---- Trotterization (1st-order) -> IBMDigital circuits: ----";
  let r = trotter_step err t lp in
  let nterm = Stdlib.List.length lp in
  let npau = r * nterm in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp( (float_of_int nterm) *. t /. (float_of_int r)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor r;
  try
    translate_lowp2circ_std err t lp nq 
  with exn -> dbg "trotterStd_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn

let trotterQDrift_IBMDigital ?(verbose=false) (err : float) (t : float) (lp : lowprog) (nq : int) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IBMDigital circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in

  (* rfactor must be very close to 1 to make sure error <= expected error  *)
  let rfactor = exp(2.0 *. lambda *. t /. (float_of_int npau)) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f; relaxation factor: %f." npau lambda rfactor;
  try
    translate_lowp2circ_qdrift err t lp nq 
  with exn -> dbg "trotterQDrift_IBMDigital raise EXN: %s" (Printexc.to_string exn);
    raise exn


let abFirst_IBMDigital ?(verbose=false) (err : float) (t : float) (lp : lowprog) (nq : int) (grouping : string) =
  if verbose then dbg "---- ABLib Trotter (1st-order; grouping=%s) -> IBMDigital circuits: ----" grouping;
  let steps = trotter_step err t lp in
  let groups =
    match grouping with
    | "none" -> [lp]
    | "qwc" -> group_qwc nq lp
    | "fc" -> group_fc nq lp
    | _ -> [lp]
  in
  let nterm = Stdlib.List.length lp in
  let npau = steps * nterm in
  let rfactor = exp ((float_of_int nterm) *. t /. (float_of_int steps)) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor steps;
  let lowp = build_first_order ~steps ~groups in
  synth_digital_ibm t nq lowp


let abSecond_IBMDigital ?(verbose=false) (err : float) (t : float) (lp : lowprog) (nq : int) (grouping : string) =
  if verbose then dbg "---- ABLib Trotter (2nd-order / Strang; grouping=%s) -> IBMDigital circuits: ----" grouping;
  let steps1 = trotter_step err t lp in
  let steps =
    max 1 (int_of_float (ceil (sqrt (float_of_int steps1))))
  in
  let groups =
    match grouping with
    | "none" -> [lp]
    | "qwc" -> group_qwc nq lp
    | "fc" -> group_fc nq lp
    | _ -> [lp]
  in
  let nterm = Stdlib.List.length lp in
  let npau = 2 * steps * nterm in
  let rfactor = exp ((float_of_int nterm) *. t /. (float_of_int (max 1 steps))) in
  if verbose then dbg "Dealing with %d pauli strings; relaxation factor: %f; splitting r: %d." npau rfactor steps;
  let lowp = build_second_order ~steps ~groups in
  synth_digital_ibm t nq lowp
