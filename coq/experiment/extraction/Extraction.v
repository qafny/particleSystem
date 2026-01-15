From QBlue Require Import Main.
From QBlue Require Import QBlueUtility.

Require Coq.extraction.Extraction.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".

(* Most List functions have the same mapping, no need to define 
 open the following if the mapping is needed *)
Require Export List.
(*
Extract Inlined Constant List.fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant List.tl => "List.tl".
Extract Inlined Constant List.forallb => "List.for_all".
Extract Inlined Constant List.existsb => "List.exists".
Extract Inlined Constant List.filter => "List.filter".
Extract Inlined Constant List.hd_error => "(fun l -> List.nth_opt l 0)".
*)

(* Standard extraction from nat -> OCaml int and Z -> OCaml int. *)
Require Export QArith.
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* Inline a few operations. *)
Extraction Inline plus mult Nat.eq_dec.
Extraction Inline Z.add Z.sub Z.mul.

(* Otherwise sub will be extracted to the (undefined) string "sub". *)
Extract Inlined Constant Init.Nat.sub => "(-)".


(* Custom extraction from R -> OCaml float. *)
Require Export Reals Reals.ROrderedType.
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Ropp => "((-.) 0.0)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "( /. )".
Extract Inlined Constant sqrt => "sqrt".
Extract Inlined Constant pow => "(fun a b -> a ** Z.to_float b)".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "atan".
Extract Inlined Constant acos => "acos".
Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant Reqb => "( = )".
Extract Inlined Constant Rlt => "( < )".
Extract Inlined Constant IZR => "Float.of_int".
(* Extracting the following to dummy values to supress warnings *)
Extract Constant ClassicalDedekindReals.sig_forall_dec  => "failwith ""Invalid extracted value"" ".
Extract Constant ClassicalDedekindReals.DRealRepr  => "failwith ""Invalid extracted value"" ".

(* map R->Nat to ocaml Float.ceil function *)
Extract Constant ceilR_N =>
"fun (r: float) ->
  let k = int_of_float (Float.ceil r) in
  if k <= 0 then 0 else k".

(* Extract from C to (float * float) *)
Require Import QuantumLib.Complex.
Extract Inlined Constant C => "(float * float)".
Extract Inlined Constant RtoC => "(fun x -> (x, 0.0))".
Extract Inlined Constant Ci => "(0.0, 1.0)".
Extract Inlined Constant Cmult => "(fun (a1, a2) (b1, b2) -> (a1 *. b1 -. a2 *. b2, a1 *. b2 +. a2 *. b1))".
Extract Inlined Constant Complex.Copp => "(fun (a, b) -> (-. a, -. b))".


Set Extraction Optimize.
Separate Extraction Main.lowp Main.c1 Main.m1.





