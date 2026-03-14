open Yojson.Basic
open Unix
open Printf
  
open Analyze_utility
open Qblue_util

exception Parse_timeout of int

let analyze_one_circuit (str_input : string) (err : float) (t :  float) (flag_path : int) : (int * int * int * int * int * int * float) =
    let to_second = 30 in
    let lp = with_timeout (fun s -> Parse_timeout s) to_second (fun () -> parse_pauli str_input) in
	let nqbit = get_dim_pauli str_input in
    let (nq1, nqm, nq1_bf, nqm_bf, tc) = 
    if flag_path = 0 then
      let (cc, cir_bf, tc, r) = translation_lowprog_optimize lp nqbit err t in
      let (nq1, nqm) = summarize_counts cc nqbit r in
      let (nq1_bf, nqm_bf) = summarize_counts cir_bf nqbit r in
      (nq1, nqm, nq1_bf, nqm_bf, tc)

	else if flag_path > 0 && flag_path < 10  
      then let (cc, cir_bf, tc, r) = lowprog_to_circ ~verbose:true lp nqbit err t flag_path in
      let (nq1, nqm) = summarize_counts cc nqbit r in
      let (nq1_bf, nqm_bf) = summarize_counts cir_bf nqbit r in
      (nq1, nqm, nq1_bf, nqm_bf, tc)	

    else if flag_path = 10 then
      let (cc, tc, r, npau) = translation_lowprog_IndiAnalog lp nqbit err t in
      let (nq1, nqm) = summarize_analog_counts cc r npau in
      (nq1, nqm, nq1, nqm, tc)

    else if flag_path > 10 && flag_path < 20 then 
	  let (cc, tc, r, npau) = lowprog_to_IndiAnalog ~verbose:true lp nqbit err t flag_path in
      let (nq1, nqm) = summarize_analog_counts cc r npau in
	  (nq1, nqm, nq1, nqm, tc)

    else if flag_path = 20 then
      let (cc, tc, r, npau) = translation_lowprog_IBMAnalog lp nqbit err t in
      let (nq1, nqm) = summarize_analog_counts cc r npau in
      (nq1, nqm, nq1, nqm, tc)

    else
	  let (cc, tc, r, npau) = lowprog_to_IBMAnalog ~verbose:true lp nqbit err t flag_path in
      let (nq1, nqm) = summarize_analog_counts cc r npau in
      (nq1, nqm, nq1, nqm, tc)



    in (nqbit, List.length lp, nq1, nqm, nq1_bf, nqm_bf, tc)


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


(* return: nqbit, nterms, # single-qubit gates, # multi-qubit gates, pre-opt counts, compilation time *)
let run (err : float) (t : float) (path : string) (flag_path : int) : (int * int * int * int * int * int * float) =
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
  let path : string option ref = ref None in

  let set_path s =
    match !path with
    | None -> path := Some s
    | Some _ -> raise (Arg.Bad "Only one <file/path> positional argument is allowed")
  in

  let speclist =
    [
      ("-e", Arg.Set_float err, "Set err (float). Default: 1.0");
      ("-t", Arg.Set_float t,   "Set t (float). Default: 0.01");
      ("-p", Arg.Set_int path_flag, "Set p (int). Default: 0");
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

  let (nqubit, nterm, single_qubit_gates, multi_qubit_gates, single_qubit_gates_bfopt, multi_qubit_gates_bfopt, tc) = run !err !t path !path_flag in
  let json_data =
    `Assoc
      [ ("file_name", `String path);
        ("error", `Float !err);
        ("simu_time", `Float !t);
        ("path_flag", `Int !path_flag);
		("nqubit", `Int nqubit);
		("npau", `Int nterm);
        ("compilation_time", `Float tc);
        ("single_qubit_gates", `Int single_qubit_gates);
        ("multi_qubit_gates", `Int multi_qubit_gates);
        ("single_qubit_gates_bfopt", `Int single_qubit_gates_bfopt);
        ("multi_qubit_gates_bfopt", `Int multi_qubit_gates_bfopt) ]
  in
  Yojson.Basic.pretty_to_channel Stdlib.stdout json_data;
  output_char Stdlib.stdout '\n';
  flush Stdlib.stdout
