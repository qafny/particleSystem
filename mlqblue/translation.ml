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
  let npau = r * (Stdlib.List.length lp) in
  if verbose then dbg "Dealing with %d pauli strings" npau;
  translate_lowp2circ_std err t lp nq 


let trotterQDrift_IBMDigital ?(verbose=false) (err : float) (t : float) (lp : lowprog) (nq : int) =
  (* Set seed to reproduce results *)
  Random.init 10;

  if verbose then dbg "---- Trotterization (QDrift) -> IBMDigital circuits: ----";
  let npau = qdrift_step err t lp in
  let lambda = sum_w lp (Stdlib.List.length lp) in
  if verbose then dbg "Dealing with %d pauli strings; lambda = %f" npau lambda;
  translate_lowp2circ_qdrift err t lp nq 



