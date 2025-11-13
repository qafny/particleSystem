From Coq Require Import Extraction.
(* Require Import Reals. 
Require Import Psatz.
Require Import List. 
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueCompiler. *)


Require Import QBlue.Main.
Require Coq.extraction.ExtrOcamlBasic.
Require ExtrOcamlList.
Require ExtrOcamlR.
Require ExtrOcamlNatZ.
Require ExtrOcamlC.

Set Extraction Optimize.
Separate Extraction Main.lowp Main.c1.




