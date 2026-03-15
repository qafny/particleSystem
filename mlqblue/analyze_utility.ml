open Printf
open Str
open QBlueSyntax
open QBlueCompile
open QBlueSynthDigital

open Lexing
open Parserlib.Parser
open Parserlib.Lexer

open ExtractionGateSet
open Voqc.Qasm
open Translation
open Qblue_util

let translation_timeout_seconds = 3600
exception Compile_timeout of int


let rec count_U1_ocaml (c : coq_U ucom) : int =
  match c with
  | Coq_useq (c1, c2) -> count_U1_ocaml c1 + count_U1_ocaml c2
  | Coq_uapp (_, U_U1 _, _) -> 1
  | Coq_uapp (_, _, _) -> 0


(* -2 read files of strings *)
let read_string_file (filename : string) : string =
  dbg "Analyzing %s:" filename;
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s


(* find dimension of string *)
let get_dim_pauli (input : string) : int =
  let helper s =  
  let re = regexp "\\*[ \t\r\n]*\\([IXYZ]+\\)\\([ \t\r\n]\\|[+-]\\|$\\)" in
  try
    ignore (search_forward re s 0);   (* find first occurrence anywhere *)
    Some (matched_group 1 s)
  with Not_found ->
    None
  in

  match (helper input) with
  | None -> 0
  | Some op -> String.length op


(* -1 parse string into lowprog *)
exception Pauli_parse_error of string

let parse_pauli (input : string) : lowprog =
  let lexbuf = Lexing.from_string input in
  try
    let lp = Parserlib.Parser.program Parserlib.Lexer.token lexbuf in
	dbg "Length of Pauli String %d\n" (List.length lp);
    lp

  with
  | Parserlib.Parser.Error ->
      let msg =
        Printf.sprintf "Parser error near offset %d (lexeme=%S)"
          (Lexing.lexeme_start lexbuf) (Lexing.lexeme lexbuf)
      in raise (Pauli_parse_error msg)
  | Parserlib.Lexer.LexError msg ->
      let msg =
        Printf.sprintf "Lexer error near offset %d (lexeme=%S): %s"
          (Lexing.lexeme_start lexbuf) (Lexing.lexeme lexbuf) msg
      in raise (Pauli_parse_error msg)


(* 0.1 lowprog -> circ *)
let lowprog_to_circ ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) (flag_path : int) =
  Qblue_util.with_timeout (fun s -> Compile_timeout s) translation_timeout_seconds (fun () ->
    match flag_path with
    | 1 -> trotterStd_IBMDigital ~verbose:verbose lp nq err t
    | 2 -> trotter2nd_IBMDigital ~verbose:verbose lp nq err t
    | 3 -> trotterQDrift_IBMDigital ~verbose:verbose lp nq err t
    | 4 -> trotterMarQSim_CNOT_IBMDigital ~verbose:verbose lp nq err t
    | 5 -> trotterMarQSim_mix_IBMDigital ~verbose:verbose lp nq err t
    | 6 -> trotterMarQdrift_CNOT_IBMDigital ~verbose:verbose lp nq err t
    | _ -> trotterMarQdrift_mix_IBMDigital ~verbose:verbose lp nq err t
  )

let lowprog_to_IndiAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) (flag_path : int) =
  Qblue_util.with_timeout (fun s -> Compile_timeout s) translation_timeout_seconds (fun () ->
    match flag_path with
    | 11 -> trotterStd_IndiAnalog ~verbose:verbose lp nq err t
    | 12 -> trotter2nd_IndiAnalog ~verbose:verbose lp nq err t
    | 13 -> trotterQDrift_IndiAnalog ~verbose:verbose lp nq err t
    | 14 -> trotterMarQSim_CNOT_IndiAnalog ~verbose:verbose lp nq err t
    | 15 -> trotterMarQSim_mix_IndiAnalog ~verbose:verbose lp nq err t
    | 16 -> trotterMarQdrift_CNOT_IndiAnalog ~verbose:verbose lp nq err t
    | _ -> trotterMarQdrift_mix_IndiAnalog ~verbose:verbose lp nq err t
  )

let lowprog_to_IBMAnalog ?(verbose=false) (lp : lowprog) (nq : int) (err : float) (t : float) (flag_path : int) =
  Qblue_util.with_timeout (fun s -> Compile_timeout s) translation_timeout_seconds (fun () ->
    match flag_path with
    | 21 -> trotterStd_IBMAnalog ~verbose:verbose lp nq err t
    | 22 -> trotter2nd_IBMAnalog ~verbose:verbose lp nq err t
    | 23 -> trotterQDrift_IBMAnalog ~verbose:verbose lp nq err t
    | 24 -> trotterMarQSim_CNOT_IBMAnalog ~verbose:verbose lp nq err t
    | 25 -> trotterMarQSim_mix_IBMAnalog ~verbose:verbose lp nq err t
    | 26 -> trotterMarQdrift_CNOT_IBMAnalog ~verbose:verbose lp nq err t
    | _ -> trotterMarQdrift_mix_IBMAnalog ~verbose:verbose lp nq err t
)


let rec get_dim_aux (u : coq_U ucom) (acc : int) : int =
  match u with
  | Coq_useq (u1, u2) -> get_dim_aux u1 (get_dim_aux u2 acc)
  | Coq_uapp (_, _, qs) -> Stdlib.List.fold_left Stdlib.max acc qs

let get_dim (u : coq_U ucom) : int =
  1 + get_dim_aux u 0


(* write to qasm file *)
let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (1, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (1, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (1, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (1, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (1, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (2, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_CU1 (r), [a;b]) -> (fprintf oc "cu1(%f) q[%d], q[%d];\n" r a b ; k ())
  | Coq_uapp (2, U_CH, [a;b]) -> (fprintf oc "ch q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (3, U_CCU1 (r), [a;b;c]) -> (fprintf oc "ccu1(%f) q[%d], q[%d], q[%d];\n" r a b c ; k ())
  | Coq_uapp (3, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (4, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" a b c d ; k ())
  (* badly typed case (e.g. App2 of U_H) *)
  | _ -> failwith "ERROR: Failed to write qasm file"

let write_qasm_file fname (u : coq_U ucom) =
  try
    let dim = get_dim u in
    let oc = open_out fname in
    (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
     fprintf oc "qreg q[%d];\n" dim;
     fprintf oc "\n";
     ignore(sqir_to_qasm oc (decompose_to_voqc_gates u) (fun _ -> ()));
     ignore(fprintf oc "\n");
     close_out oc)
  with exn -> 
    dbg "write_qasm_file raised %s" (Printexc.to_string exn);
    raise exn


(* function to count gates 
  Output order: X, H, U1, CX, CH, CU1, CCX, CCU1, C3X *)
let rec count_gates_aux (u : coq_U ucom) acc =
  let (x,h,u1,cx,ch,cu1,ccx,ccu1,c3x) = acc in
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (1, U_X, _) -> (1+x,h,u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (1, U_H, _) -> (x,1+h,u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (1, U_U1 _, _) -> (x,h,1+u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CX, _) -> (x,h,u1,1+cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CH, _) -> (x,h,u1,cx,1+ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CU1 _, _) -> (x,h,u1,cx,ch,1+cu1,ccx,ccu1,c3x)
  | Coq_uapp (3, U_CCX, _) -> (x,h,u1,cx,ch,cu1,1+ccx,ccu1,c3x)
  | Coq_uapp (3, U_CCU1 _, _) -> (x,h,u1,cx,ch,cu1,ccx,1+ccu1,c3x)
  | Coq_uapp (4, U_C3X, _) -> (x,h,u1,cx,ch,cu1,ccx,ccu1,1+c3x)
  (* unexpected gate type *)
  | _ -> failwith "ERROR: Failed to count gates"


let count_gates u = count_gates_aux u (0,0,0,0,0,0,0,0,0)



(* 1. circuit -> qasm file *)
let print_and_write_qasm circ fname =
  let (x,h,u1,cx,ch,cu1,ccx,ccu1,c3x) = count_gates circ in
  (printf "\t%d qubits, { " (get_dim circ);
  if x > 0 then printf "X : %d, " x;
  if h > 0 then printf "H : %d, " h;
  if u1 > 0 then printf "U1 : %d, " u1;
  if cx > 0 then printf "CX : %d, " cx;
  if ch > 0 then printf "CH : %d, " ch;
  if cu1 > 0 then printf "CU1 : %d, " cu1;
  if ccx > 0 then printf "CCX : %d, " ccx;
  if ccu1 > 0 then printf "CCU1 : %d, " ccu1;
  if c3x > 0 then printf "C3X : %d, " c3x;
  printf " }\n%!";
  write_qasm_file fname circ);;

let log2 m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0))

let log2up m = int_of_float (ceil (log10 (float_of_int (2 * m)) /. log10 2.0))

let summarize_counts (cc : Main.circ) (nqbit : int) (r : int) : int * int =
  let nqm = voqc_count_CX nqbit cc in
  let nq1 = voqc_count_total nqbit cc - nqm in
  (* # single-qubits, multiple-qubits  *)
  (r * nq1, r * nqm)


let translation_lowprog_optimize (lp : lowprog) (nqbit : int) (err : float) (t : float) =
  let best_path = ref 100 in
  let ts_tot = ref 0.0 in
  let best_score = ref max_int in 
  for flag_path = 1 to 7 do
    let (cc, _, ts, r) = lowprog_to_circ ~verbose:true lp nqbit err t flag_path in 
    let (nq1, score) = summarize_counts cc nqbit r in
	ts_tot := !ts_tot +. ts;
	dbg "Path flag: %d; # Single-bit gates: %d; # CNOT gates: %d.\n" flag_path nq1 score;
	if score < !best_score then 
	begin
      best_score := score;
      best_path := flag_path;
    end
  done; 
  let (c1, c_bf, _, r) = lowprog_to_circ ~verbose:false lp nqbit err t !best_path in
  (c1, c_bf, !ts_tot, r)

let summarize_analog_counts (cc : ugate list) (r : int) (npau : int) : int * int =
  let ntot = r * (List.length cc) in
  let nq1 = ntot - npau in
  (* # single-qubits, multiple-qubits  *)
  (nq1, npau)

let translation_lowprog_IndiAnalog (lp : lowprog) (nqbit : int) (err : float) (t : float) =
  let best_path = ref 100 in
  let ts_tot = ref 0.0 in
  let best_score = ref max_int in
  for flag_path = 11 to 17 do
    let (cc, ts, r, npau) = lowprog_to_IndiAnalog ~verbose:true lp nqbit err t flag_path in
	(* currently use number of pauli strings *)
	let (nq1, score) = summarize_analog_counts cc nqbit npau in
    ts_tot := !ts_tot +. ts;
	dbg "Path flag: %d; # Single-bit gates: %d; # multi-bit gates: %d.\n" flag_path nq1 score;
    if score < !best_score then
    begin
      best_score := score;
      best_path := flag_path;
    end
  done;
  let (cc, _, r, npau) = lowprog_to_IndiAnalog ~verbose:false lp nqbit err t !best_path in
  (cc, !ts_tot, r, npau)

let translation_lowprog_IBMAnalog (lp : lowprog) (nqbit : int) (err : float) (t : float) =
  let best_path = ref 100 in
  let ts_tot = ref 0.0 in
  let best_score = ref max_int in
  for flag_path = 21 to 27 do
    let (cc, ts, r, npau) = lowprog_to_IBMAnalog ~verbose:true lp nqbit err t flag_path in
    (* currently use number of pauli strings *)
    let (nq1, score) = summarize_analog_counts cc nqbit npau in
    ts_tot := !ts_tot +. ts;
    dbg "Path flag: %d; # Single-bit gates: %d; # multi-bit gates: %d.\n" flag_path nq1 score;
    if score < !best_score then
    begin
      best_score := score;
      best_path := flag_path;
    end
  done;
  let (cc, _, r, npau) = lowprog_to_IBMAnalog ~verbose:false lp nqbit err t !best_path in
  (cc, !ts_tot, r, npau)



(*		
let read_qasm_and_optimize ?(verbose=false) fname =
  let (c0, n) = read_qasm fname in 
  (* Convert to the RzQ gate set and print more statistics *)
  let c1 = voqc_convert_to_rzq n c0 in

  (* Map to the 5 qubit LNN ring architecture *)
  let cg = voqc_make_lnn_ring n 5 in
  let la = voqc_trivial_layout n 5 in
  let c2 = voqc_decompose_swaps (swap_route c1 la cg (voqc_lnn_ring_path_finding_fun 5)) cg in

  (* Optimize again *)
  let c3 = optimize c2 in
  if verbose then print_optimization_detail n c0 c1 c2 c3;
  (c0, c3, n);;
*)


(*
(* 3. write result.txt for a bunch of qasm files under a dir *)
let summarize_results dirname rst_file =
  let rst = open_out rst_file in

  let _ = fprintf rst "Name, #qubits, #gates (original), #gates (optimized), #U2 gates (optimized)\n" in

  let helper af = 
    let (c0, c1, n) = read_qasm_and_optimize af in
    fprintf rst "%s, %d, %d, %d, %d\n" af n (count_total c0) (count_total c1) (count_U2 c1) in

  let qasm_files = List.map (fun f -> Filename.concat dirname f)
    (Stdlib.List.filter (fun x -> Filename.extension x = ".qasm") (Array.to_list (Sys.readdir dirname))) in
	
  Stdlib.List.iter helper qasm_files;;
*)

(* flow from input string to qasm file *)
(* let string_to_qasm ?(filename="") (str_input : string) (err : float) (t : float) (fout : string) (flag_path : int) =
  try
    let lp = parse_pauli str_input in
    let nqbit = get_dim_pauli str_input in
    let ham = lowprog_to_circ err t nqbit lp flag_path in
    write_qasm_file fout ham

  with
  | Pauli_parse_error msg ->
      dbg "SKIP file=%S: %s" filename msg;
      ()
 
  | exn ->
      dbg "SKIP file=%S due to EXN: %s" filename (Printexc.to_string exn);
      ()
*)


(*
let string_files_to_qasm_files (err : float) (t : float) (input_files : string list) (out_dir : string) = 
  let helper af =
    let s = read_string_file af in
	let fout = af ^ ".qasm" in
	string_to_qasm ~filename:af s err t fout 0 in
  Stdlib.List.iter helper input_files;;
*)
