let read_all ic =
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
  with End_of_file -> ());
  Buffer.contents buf

let find_python_path exe_name =
  let is_executable path =
    Sys.file_exists path
    &&
    try
      Unix.access path [ Unix.X_OK ];
      true
    with Unix.Unix_error _ -> false
  in
  let path_env = try Sys.getenv "PATH" with Not_found -> "" in
  let dirs = String.split_on_char ':' path_env in
  let rec loop = function
    | [] -> None
    | dir :: rest ->
        let candidate = Filename.concat dir exe_name in
        if is_executable candidate then Some candidate else loop rest
  in
  loop dirs

let file_exists path =
  try Unix.(stat path).st_kind = S_REG with Unix.Unix_error _ -> false

let make_absolute path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

let find_api_path () =
  let cwd_api = Filename.concat (Sys.getcwd ()) "qbluelib/ml/api.py" in
  let exe_dir = make_absolute (Filename.dirname Sys.executable_name) in
  let build_api = Filename.concat exe_dir "qbluelib/ml/api.py" in
  let env_api =
    try Some (Sys.getenv "QBLUE_API_PY") with Not_found -> None
  in
  let candidates =
    match env_api with
    | Some path -> [ path; cwd_api; build_api ]
    | None -> [ cwd_api; build_api ]
  in
  let rec loop = function
    | [] ->
        failwith
          "Could not locate api.py. Set QBLUE_API_PY or run from the project root."
    | path :: rest ->
        let abs_path = make_absolute path in
        if file_exists abs_path then abs_path else loop rest
  in
  loop candidates

let get_matrix_pgc list_coef_json cnot_matrix_json singleq_matrix_json =
  let python_bin =
    match find_python_path "python3" with
    | Some p -> p
    | None -> "/usr/bin/python3"
  in
  let api_path = find_api_path () in
  let extra_args =
    match singleq_matrix_json with
    | Some s -> [| list_coef_json; cnot_matrix_json; s |]
    | None -> [| list_coef_json; cnot_matrix_json |]
  in
  let py_args =
    Array.append [| python_bin; api_path; "genmat_gate_cancellation" |] extra_args
  in
  let ic = Unix.open_process_args_in python_bin py_args in
  let output = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 -> String.trim output
  | Unix.WEXITED code ->
      failwith (Printf.sprintf "python api failed with exit code %d" code)
  | Unix.WSIGNALED signal ->
      failwith (Printf.sprintf "python api killed by signal %d" signal)
  | Unix.WSTOPPED signal ->
      failwith (Printf.sprintf "python api stopped by signal %d" signal)
