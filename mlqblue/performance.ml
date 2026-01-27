open Unix

open Analyze_utility


let analyze_one_circuit (str_input : string) =
  let lp = parse_pauli str_input in
  let fout = "tmp.qasm" in
  let ham = lowgrog_to_circ lp in
  let _ = print_and_write_qasm ham fout in
  read_qasm_and_optimize1 fout;;
 


let is_txt_file (path : string) : bool =
  Filename.check_suffix path ".txt"

let read_file (filename : string) : string =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let rec collect_txt_files (dir : string) : string list =
  let dh = opendir dir in
  let rec loop acc =
    match readdir dh with
    | entry ->
      if entry = "." || entry = ".." then loop acc
      else
        let path = Filename.concat dir entry in
        match (Unix.lstat path).st_kind with
        | S_DIR ->
            let acc' = collect_txt_files path @ acc in
            loop acc'
        | S_REG ->
            if is_txt_file path then loop (path :: acc) else loop acc
        | _ ->
            loop acc
    | exception End_of_file ->
        closedir dh;
        List.rev acc
  in
  loop []



let main () = 
  if Array.length Sys.argv <> 2 then (
    prerr_endline "Usage: dune exec -- ./performance.exe <file/path>";
    exit 2
  );

  let path = Sys.argv.(1) in
  match (Unix.lstat path).st_kind with
  | S_DIR ->
      let files = collect_txt_files path in
      Printf.printf "Found %d .txt files under %s\n" (List.length files) path;
      List.iter
        (fun f ->
          let s = read_file f in
          Printf.printf "---- %s (%d chars) ----\n" f (String.length s);
          ())
        files
  | S_REG ->
      if not (is_txt_file path) then (
        prerr_endline "Error: input file is not a .txt file";
        exit 1
      );
      let s = read_file path in
      Printf.printf "---- %s ----\n" path;
	  ignore (analyze_one_circuit s);

  | _ ->
      prerr_endline "Error: path is neither a regular file nor a directory";
      exit 1;;


let () = main ()


