open Unix
open Printf

open Analyze_utility
open Util


let analyze_one_circuit (str_input : string) (err : float) (t :  float) (flag_path : int) =
    Printf.printf  "Start analyze_one_circuit\n";
	flush Stdlib.stdout;
    let lp = parse_pauli str_input in
    Printf.printf  "After parser";
	flush Stdlib.stdout;
	let nqbit = get_dim_pauli str_input in
    Printf.printf "After getting qubit %d\n%!" nqbit;
	flush Stdlib.stdout;
	if flag_path = 0 then translation_lowprog_optimize lp nqbit err t
	else lowprog_to_circ ~verbose:true err t nqbit lp flag_path 
	


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


let run (err : float) (t : float) (fout : string) (path : string) (flag_path : int) : unit =
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
      ignore (analyze_one_circuit s err t flag_path)

  | _ ->
      prerr_endline "Error: path is neither a regular file nor a directory";
      exit 1


(* CLI entrypoint *)
let () =
  (* default values when -e / -t are not provided *)
  let err  = ref 1.0 in
  let t    = ref 0.01 in
  let fout = ref "result.txt" in
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
      ("-o", Arg.Set_string fout,   "Set o (string). Default: result.txt");
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

  run !err !t !fout path !path_flag

