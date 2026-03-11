open Yojson.Basic
open Unix
open Printf
  
open Analyze_utility
open Qblue_util

exception Parse_timeout of int

let analyze_one_circuit (str_input : string) (err : float) (t :  float) (flag_path : int) : (int * int * int * int) =
    let to_second = 30 in
    let lp = with_timeout (fun s -> Parse_timeout s) to_second (fun () -> parse_pauli str_input) in
	let nqbit = get_dim_pauli str_input in
    let (nq1, nqm) = 
    if flag_path = 0 then translation_lowprog_optimize lp nqbit err t

	else if flag_path > 0 && flag_path < 10  
      then let (cc, r) = lowprog_to_circ ~verbose:true lp nqbit err t flag_path in
	  summarize_counts cc nqbit r

    else if flag_path = 10 then translation_lowprog_analog lp nqbit err t

    else 
	  let (cc, r, npau) = lowprog_to_analog_circ ~verbose:true lp nqbit err t flag_path in
	  summarize_analog_counts cc r npau

    in (nqbit, List.length lp, nq1, nqm)


let is_txt_file (path : string) : bool =
  Filename.check_suffix path ".txt"


let rec collect_txt_files (dir : string) : string list =
  let dh = Unix.opendir dir in
  let rec loop acc =
    try
      let entry = Unix.readdir dh in
      if entry = "." || entry = ".." then loop acc
      else
        let path = Filename.concat dir entry in
        match (Unix.lstat path).st_kind with
        | Unix.S_DIR ->
            loop (collect_txt_files path @ acc)
        | Unix.S_REG ->
            if is_txt_file path then loop (path :: acc) else loop acc
        | _ ->
            loop acc
    with
    | End_of_file ->
        Unix.closedir dh;
        List.rev acc
  in
  loop []


(* return: nqbit, nterms, # single-qubit gates, # multi-qubit gates *)
let run (err : float) (t : float) (path : string) (flag_path : int) : (int * int * int * int) =
  dbg "Expected error: %f;   t: %f" err t;
  match (Unix.lstat path).st_kind with
  | Unix.S_DIR ->
      prerr_endline "Error: path is neither a regular file nor a directory";
      exit 1
     (* let files = collect_txt_files path in
      let out_dir = path ^ "_qasm" in
      string_files_to_qasm_files err t files out_dir;
      summarize_results path fout
*)

  | Unix.S_REG ->
      if not (is_txt_file path) then (
        prerr_endline "Error: input file is not a .txt file";
        exit 1
      );
      let s = read_string_file path in
      analyze_one_circuit s err t flag_path

  | _ ->
      prerr_endline "Error: path is neither a regular file nor a directory";
      exit 1


(* CLI entrypoint *)
let () =
  (* default values when -e / -t are not provided *)
  let err  = ref 1.0 in
  let t    = ref 0.01 in
  let path_flag = ref 0 in
  let grouping = ref "none" in
  let path : string option ref = ref None in

  let set_path s =
    match !path with
    | None -> path := Some s
    | Some _ -> raise (Arg.Bad "Only one <file/path> positional argument is allowed")
  in

  let set_grouping s =
    match String.lowercase_ascii s with
    | "none" | "qwc" | "fc" -> grouping := String.lowercase_ascii s
    | _ ->
        raise (Arg.Bad "Invalid -g value. Expected one of: none|qwc|fc")
  in

  let speclist =
    [
      ("-e", Arg.Set_float err, "Set err (float). Default: 1.0");
      ("-t", Arg.Set_float t,   "Set t (float). Default: 0.01");
      ("-p", Arg.Set_int path_flag, "Set p (int). Default: 0");
      ("-g", Arg.String set_grouping, "Set grouping: none|qwc|fc. Default: none");
    ]
  in

  let usage =
    "Usage: dune exec -- ./performance.exe <file/path> [-e <float>] [-t <float>] [-p <int>]"
  in

  Arg.parse speclist set_path usage;

  let path =
    match !path with
    | Some p -> p
    | None ->
        prerr_endline usage;
        exit 2
  in

  let (nqubit, nterm, single_qubit_gates, multi_qubit_gates) = run !err !t path !path_flag in
  let json_data =
    `Assoc
      [ ("file_name", `String path);
        ("error", `Float !err);
        ("time", `Float !t);
        ("path_flag", `Int !path_flag);
		("nqubit", `Int nqubit);
		("npau", `Int nterm);
        ("single_qubit_gates", `Int single_qubit_gates);
        ("multi_qubit_gates", `Int multi_qubit_gates) ]
  in
  Yojson.Basic.pretty_to_channel Stdlib.stdout json_data;
  output_char Stdlib.stdout '\n';
  flush Stdlib.stdout
