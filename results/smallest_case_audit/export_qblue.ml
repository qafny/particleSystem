open UnitaryListRepresentation
open FullGateSet.FullGateSet
let dump name circ =
 let oc = open_out name in
 Printf.fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[8];\n";
 List.iter (function
 | App1 (g,a) -> let s = match g with
   | U_I -> "id" | U_X -> "x" | U_Y -> "y" | U_Z -> "z" | U_H -> "h"
   | U_S -> "s" | U_T -> "t" | U_Sdg -> "sdg" | U_Tdg -> "tdg"
   | U_Rzq q -> Printf.sprintf "rz(%.17g)" (Float.pi *. float_of_int q.QArith_base.coq_Qnum /. float_of_int q.QArith_base.coq_Qden)
   | U_Rx r -> Printf.sprintf "rx(%.17g)" r | U_Ry r -> Printf.sprintf "ry(%.17g)" r
   | U_Rz r -> Printf.sprintf "rz(%.17g)" r | U_U1 r -> Printf.sprintf "u1(%.17g)" r
   | U_U2 (r,s) -> Printf.sprintf "u2(%.17g,%.17g)" r s
   | U_U3 (r,s,t) -> Printf.sprintf "u3(%.17g,%.17g,%.17g)" r s t
   | _ -> failwith "one-qubit gate" in Printf.fprintf oc "%s q[%d];\n" s a
 | App2 (U_CX,a,b) -> Printf.fprintf oc "cx q[%d],q[%d];\n" a b
 | _ -> failwith "unexpected gate") circ;
 close_out oc;
 Printf.printf "%s: 1q=%d cx=%d\n%!" name (List.length circ - Main.count_CX 8 circ) (Main.count_CX 8 circ)
let () =
 let ic = open_in "mlqblue/DataSet1/small/MarqSim_Ar_60.txt" in
 let lp = Parserlib.Parser.program Parserlib.Lexer.token (Lexing.from_channel ic) in
 close_in ic;
 let r = QBlueTrotter.trotter_step_2nd_order 0.1 0.7854 (QBlueUtility.lowprog2norm_prog lp) in
 Printf.printf "steps=%d\n%!" r;
 let dir = "results/smallest_case_audit/" in
 dump (dir ^ "qblue_actual_before.qasm") (QBlueCompile.translate_lowp2circ_2ndTrotter 0.1 0.7854 lp 8 (QBlueSynthDigital.ibmdigi_to_rzq 8));
 dump (dir ^ "qblue_actual_after.qasm") (QBlueCompile.translate_lowp2circ_2ndTrotter 0.1 0.7854 lp 8 (QBlueSynthDigital.ibmdigi_voqc_optimize 8));
 List.iter (fun steps ->
 let scaled = QBlueUtility.mult_r_hplus (1. /. (2. *. float_of_int steps)) (List.rev lp @ lp) in
 let raw = QBlueSynthDigital.synth_digital_ibm 0.7854 8 scaled in
 let prefix = dir ^ "qblue_step" ^ string_of_int steps in
 dump (prefix ^ "_unrouted.qasm") (QBlueSynthDigital.cvt_egate_fullgate 8 raw);
 dump (prefix ^ "_routed.qasm") (QBlueSynthDigital.ibmdigi_to_rzq 8 raw);
 dump (prefix ^ "_optimized.qasm") (QBlueSynthDigital.ibmdigi_voqc_optimize 8 raw)
 ) [1; r]
let () =
 let lp = Parserlib.Parser.program Parserlib.Lexer.token (Lexing.from_string "+ 1.0 * ZZIIIIII") in
 dump "results/smallest_case_audit/qblue_minimal_ZZ.qasm"
  (QBlueSynthDigital.cvt_egate_fullgate 8 (QBlueSynthDigital.synth_digital_ibm 0.1 8 lp))
