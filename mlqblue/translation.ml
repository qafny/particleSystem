open Printf
open Random

open QBlueSyntax
open QBlueSynthDigital
open QBlueTrotter
open QBlueQdrift
open QBlueCompile
open Util


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



