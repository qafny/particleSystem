open Printf
open Lexing
open Parserlib.Parser
open Parserlib.Lexer

open ExtractionGateSet
open Voqc.Qasm
open Voqc.Qasm
open Voqc.Main
open QBlueCompile



let parse_pauli input =
 let lexbuf = Lexing.from_string input in
  try
     Parserlib.Parser.program Parserlib.Lexer.token lexbuf 
    with
  | Parserlib.Parser.Error ->
      Printf.eprintf "Parser error near offset %d (lexeme=%S)\n"
        (Lexing.lexeme_start lexbuf) (Lexing.lexeme lexbuf);
    exit 1	

(* 0.1 lowprog -> circ *)
let lowgrog_to_circ lp =
  translate_lowp2circ 1.0 1.0 lp 5


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
  let dim = get_dim u in
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc (decompose_to_voqc_gates u) (fun _ -> ()));
   ignore(fprintf oc "\n");
   close_out oc)

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



(* 2.1 qasm file -> optimize -> gate count *)
let read_qasm_and_optimize fname =
  let (c, n) = read_qasm fname in 
  (optimize c, n);;


(* 2.2 qasm file -> optimize path 2 -> gate count *)
let read_qasm_and_optimize1 fname = 
  let (c0, n) = read_qasm fname in
  let _ = printf "Input circuit has %d gates and uses %d qubits.\n" (count_total c0) n in
  
  (* Convert to the RzQ gate set and print more statistics *)
  let c1 = convert_to_rzq c0 in
  let _ = printf "After decomposition to the RzQ gate set, the circuit uses %d gates : { H : %d, X : %d, Rzq : %d, CX : %d }.\n"
            (count_total c1) (count_H c1) (count_X c1) (count_Rzq c1) (count_CX c1) in
  
  (* Map to the 5 qubit LNN ring architecture *)
  let cg = make_lnn_ring 5 in
  let la = trivial_layout 5 in
  let c2 = decompose_swaps (swap_route c1 la cg (lnn_ring_path_finding_fun 5)) cg in
  let _ = printf "After mapping to 5bit LNN ring arch, the circuit uses %d gates : { H : %d, X : %d, Rzq : %d, CX : %d }.\n"
            (count_total c2) (count_H c2) (count_X c2) (count_Rzq c2) (count_CX c2) in
  
  (* Optimize again *)
  let c3 = optimize c2 in
  let _ = printf "After optimization, the circuit uses %d gates : { U1 : %d, U2 : %d, U3 : %d, CX : %d }.\n"
    (count_total c3) (count_U1 c3) (count_U2 c3) (count_U3 c3) (count_CX c3) in
  (c3, n);;


(* 3. write result.txt for a bunch of files under a dir *)
let gen_counts_dir dirname =

  let rst = open_out "result.txt" in

  let _ = fprintf rst "Name, #qubits, #gates\n" in

  let helper af = 
    let (c, n) = read_qasm_and_optimize af in
    fprintf rst "%s, %d, %d\n" af n (count_total c) in

  let qasm_files = List.map (fun f -> Filename.concat dirname f)
    (Stdlib.List.filter (fun x -> Filename.extension x = ".qasm") (Array.to_list (Sys.readdir dirname))) in
	
  Stdlib.List.iter helper qasm_files;;



(*

(* Argument parsing *)
let parse_args () : string =
  let f = ref "" in
  let usage = "usage: " ^ Sys.argv.(0) ^ " -f string" in
  let speclist = [
    ("-f", Arg.Set_string f, ": input program");
  ] in
  Arg.parse speclist (fun x -> raise (Arg.Bad ("Bad argument: " ^ x))) usage;
  if !f = "" 
  then (
    Printf.eprintf "ERROR: Input file (-f) required.\n";
    exit 2) 
  else !f


let fout = parse_args ();;
gen_qasm_from_lowp (Main.lowp) fout;;
*)


