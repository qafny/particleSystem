From SQIR Require Import ExtractionGateSet.

From QBlue Require Import QBlueUtility.
From QBlue Require Import QBlueCompile.
From QBlue Require Import QBlueSynthDigital.

Require Coq.extraction.Extraction.
(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".

(* Most List functions have the same mapping, no need to define 
 open the following if the mapping is needed *)
(* Blacklist make extraction produce List0 rather than List, which can shadow Stdlib.List funcs *)
Extraction Blacklist List.
Require Import List.
Extract Inlined Constant List.fold_left => "(fun f l acc -> Stdlib.List.fold_left f acc l)".
Extract Inlined Constant List.fold_right => "(fun f acc l -> Stdlib.List.fold_right f l acc)".
Extract Inlined Constant List.nth_error => "Stdlib.List.nth_opt".
Extract Inlined Constant List.hd_error => "(fun l -> Stdlib.List.nth_opt l 0)".
Extract Inlined Constant List.length => "Stdlib.List.length".
Extract Inlined Constant List.app => "Stdlib.List.append".
Extract Inlined Constant List.map => "Stdlib.List.map".
Extract Inlined Constant List.rev => "Stdlib.List.rev".
Extract Inlined Constant List.rev_append => "Stdlib.List.rev_append".
Extract Inlined Constant List.forallb => "Stdlib.List.for_all".
Extract Inlined Constant List.existsb => "Stdlib.List.exists".
Extract Inlined Constant List.filter => "Stdlib.List.filter".
Extract Inlined Constant List.tl => "Stdlib.List.tl".

(* Standard extraction from nat -> OCaml int and Z -> OCaml int. *)
Require Export QArith.
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* Inline a few operations. *)
Extraction Inline plus mult Nat.eq_dec.
Extraction Inline Z.add Z.sub Z.mul.

(* Otherwise sub will be extracted to the (undefined) string "sub". *)
Extract Inlined Constant Init.Nat.sub => "(-)".
Extract Inlined Constant INR => "Float.of_int".
Extract Inlined Constant IZR => "Float.of_int".


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
Extract Inlined Constant Rabs => "abs_float".
Extract Inlined Constant pow => "(fun a b -> a ** (float_of_int b))".
Extract Inlined Constant ln => "log".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "atan".
Extract Inlined Constant acos => "acos".
Extract Inlined Constant exp => "Float.exp".
Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant QBlueUtility.Reqb => "Stdlib.( = )".
Extract Inlined Constant ChangeRotationBasis.Rltb => "Stdlib.( < )".
Extract Inlined Constant QBlueUtility.Rltb => "Stdlib.( < )".
Extract Inlined Constant Coq.Reals.ROrderedType.Reqb => "Stdlib.( = )".

(* Map Q<->R with the generated QArith_base.ml *)
Extract Inlined Constant Coq.Reals.Rdefinitions.Q2R =>
"(fun q ->
   (Float.of_int q.QArith_base.coq_Qnum) /.
   (Float.of_int q.QArith_base.coq_Qden))".

Extract Inlined Constant FullGateSet.R2Q =>
"(fun x ->
   let scale = 1000000000 in
   let n = int_of_float (Float.round (x *. Float.of_int scale)) in
   { QArith_base.coq_Qnum = n; QArith_base.coq_Qden = scale })".


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

(* Extract Random generators to Ocaml Random *)
Extract Inlined Constant random_float => "Random.float".
From QBlue Require Import QBlueMarQSim.
Extract Inlined Constant GenPgc => "Bridge.get_matrix_pgc".


Set Extraction Optimize.
Cd "./extracted".
Separate Extraction
  QBlueCompile.translate_highp2circ 
  QBlueCompile.translate_lowp2circ_std 
  QBlueCompile.translate_lowp2circ_std_2nd_order 
  QBlueCompile.translate_lowp2circ_qdrift
  QBlueCompile.translate_lowp2circ_marqsim
  QBlueCompile.translate_lowp2circ_TTS_LCU
  QBlueCompile.translate_lowp2Indiana_std
  QBlueCompile.translate_lowp2Indiana_std_2nd_order 
  QBlueCompile.translate_lowp2Indiana_qdrift
  QBlueCompile.translate_lowp2Indiana_marqsim

(* gate decomposition pass *)
  ExtractionGateSet.decompose_to_voqc_gates

(* VOQC functions you want in the same local type universe *)
  QBlueSynthDigital.cvt_egate_fullgate
  QBlueSynthDigital.voqc_count_total
  QBlueSynthDigital.voqc_count_H
  QBlueSynthDigital.voqc_count_X
  QBlueSynthDigital.voqc_count_Rzq
  QBlueSynthDigital.voqc_count_CX
  QBlueSynthDigital.voqc_count_U1
  QBlueSynthDigital.voqc_count_U2
  QBlueSynthDigital.voqc_count_U3
  QBlueSynthDigital.voqc_convert_to_rzq
  QBlueSynthDigital.voqc_swap_route
  QBlueSynthDigital.voqc_decompose_swaps
  QBlueSynthDigital.voqc_optimize
  QBlueSynthDigital.voqc_make_lnn_ring
  QBlueSynthDigital.voqc_trivial_layout
  QBlueSynthDigital.voqc_lnn_ring_path_finding_fun.

 
 

