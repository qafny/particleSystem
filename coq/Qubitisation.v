(* QBlueQubitisationHigh.v – Qubitisation for second-quantised Hamiltonians *)
From SQIR Require Import ExtractionGateSet.
Require Import Reals List.
Import ListNotations.
Require Import QBlueSyntax.
Require Import QBlueGates.
Require Import QBlueParTransJwt. (* Jordan-Wigner *)
Require Import QBlueTTS.        (* Taylor series & LCU + qubitisation on lowprog *)

Open Scope R_scope.

Definition TTS_Qubitisation_high (err t : R) (nbit : nat) (H : highprog) : ucom ExtractionGateSet.U :=
  let low := highprog_to_lowprog H nbit in
  TTS_Qubitisation err t nbit low.