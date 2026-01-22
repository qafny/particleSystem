
open Analyze_utility


let analyze_one_circuit lp =
  let fout = "tmp.qasm" in
  let ham = lowgrog_to_circ lp in
  let _ = print_and_write_qasm ham fout in
  read_qasm_and_optimize1 fout;;
  
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
*)





