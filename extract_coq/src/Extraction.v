From SQIR Require Import ExtractionGateSet.

From QBlue Require Import QBlueUtility.
From QBlue Require Import QBlueCompile.
From QBlue Require Import QBlueSynthDigital.
From QBlue Require Import QBlueQuantumWalk.
From QBlue Require Import QBlueQubitization.
From QBlue Require Import QBlueQSVT.
From QBlue Require Import QBlueTTS_v4.

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
Extract Inlined Constant asin => "asin".
Extract Inlined Constant exp => "Float.exp".

(* Bessel J_k(tau): Miller backward recurrence, normalised to J_0+2*J_2+...=1 *)
Extract Constant QBlue.QBlueQuantumWalk.bessel_j =>
  "(fun k tau ->
    let tau = abs_float tau in
    if tau < 1e-15 then (if k = 0 then 1.0 else 0.0)
    else begin
      (* m robust bound: k + tau + offset based on log(1/eps) *)
      let m = max k (int_of_float tau) + 40 in
      let b = Array.make (m + 2) 0.0 in
      b.(m) <- 1e-30;
      for i = m - 1 downto 0 do
        b.(i) <- 2.0 *. float_of_int (i+1) /. tau *. b.(i+1) -. b.(i+2);
        if b.(i) > 1e100 then (for j = i to m do b.(j) <- b.(j) *. 1e-100 done)
      done;
      let sum = ref b.(0) in
      let i = ref 2 in
      while !i <= m do sum := !sum +. 2.0 *. b.(!i); i := !i + 2 done;
      if k <= m then b.(k) /. !sum else 0.0
    end)".

Extract Constant QBlue.QBlueQuantumWalk.findK_qwalk =>
  "(fun tau eps ->
    let tau = abs_float tau in
    let eps = max eps 1e-18 in
    let k_try = int_of_float (tau *. 2.0 +. 40.0 +. log (1.0 /. eps) *. 2.0) in
    let b = Array.make (k_try + 2) 0.0 in
    b.(k_try) <- 1e-30;
    for i = k_try - 1 downto 0 do
      b.(i) <- 2.0 *. float_of_int (i+1) /. tau *. b.(i+1) -. b.(i+2);
      if b.(i) > 1e100 then (for j = i to k_try do b.(j) <- b.(j) *. 1e-100 done)
    done;
    let sum = ref b.(0) in
    let i = ref 2 in
    while !i <= k_try do sum := !sum +. 2.0 *. b.(!i); i := !i + 2 done;
    let norm_b k = if k <= k_try then b.(k) /. !sum else 0.0 in
    let tail = ref 0.0 in
    let best = ref k_try in
    for k = k_try downto 1 do
      tail := !tail +. 2.0 *. abs_float (norm_b k);
      if !tail < eps then best := k - 1
    done;
    !best)".

Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant QBlueUtility.Reqb => "Stdlib.( = )".
Extract Inlined Constant ChangeRotationBasis.Rltb => "Stdlib.( < )".
Extract Inlined Constant QBlueUtility.Rltb => "Stdlib.( < )".
Extract Inlined Constant Coq.Reals.ROrderedType.Reqb => "Stdlib.( = )".
Extract Inlined Constant Rlt_dec => "( < )".
Extract Inlined Constant Rle_dec => "( <= )".
Extract Inlined Constant Req_dec => "( = )".

(* total_order_T for R is expected to return 'bool option' in the Rdefinitions module context.
   Some true -> r1 < r2, None -> r2 < r1, Some false -> r1 = r2. *)
Extract Constant total_order_T => 
"(fun r1 r2 -> if r1 < r2 then Some true else if r2 < r1 then None else Some false)".

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
Extract Constant nsampe_gatesize_est => "100".
Extract Constant ngates_per_chunk => "3000".


Set Extraction Optimize.
Cd "./extracted".
Separate Extraction
  QBlueSynth.check_2local

  QBlueTTS_v4.TTS_LCU1

  QBlueMarQSim.get_trans_CNOT
  QBlueMarQSim.get_trans_mixed
  QBlueMarQSim.get_trans_MarQdrift

  QBlueCompile.translate_highp2circ 
  QBlueCompile.translate_lowp2circ_stdTrotter 
  QBlueCompile.translate_lowp2circ_2ndTrotter 
  QBlueCompile.translate_lowp2circ_qdrift
  QBlueCompile.translate_lowp2circ_marqsim
  QBlueCompile.translate_lowp2circ_TTS_LCU
  QBlueCompile.translate_lowp2circ_qwalk
  QBlueCompile.translate_lowp2IndiAna_stdTrotter
  QBlueCompile.translate_lowp2IndiAna_2ndTrotter
  QBlueCompile.translate_lowp2IndiAna_qdrift
  QBlueCompile.translate_lowp2IndiAna_marqsim
  QBlueCompile.translate_lowp2IBMAna_stdTrotter
  QBlueCompile.translate_lowp2IBMAna_std_2ndTrotter
  QBlueCompile.translate_lowp2IBMAna_qdrift
  QBlueCompile.translate_lowp2IBMAna_marqsim
  QBlueQuantumWalk.build_qwalk_lcu_circuit
  QBlueQuantumWalk.build_state_prep
  QBlueQuantumWalk.build_inner_prep
  QBlueQuantumWalk.build_outer_prep
  QBlueQuantumWalk.findK_qwalk
  QBlueQubitization.findDegree_qsp
  QBlueQubitization.build_qubitization_circuit
  QBlueQSVT.findDegree_qsvt
  QBlueQSVT.build_qsvt_circuit
  QBlueCompile.translate_lowp2circ_qsvt

(* gate decomposition pass *)
  ExtractionGateSet.decompose_to_voqc_gates

(* VOQC functions you want in the same local type universe *)
  QBlueSynthDigital.ibmdigi_to_rzq
  QBlueSynthDigital.ibmdigi_voqc_optimize
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

 
 

