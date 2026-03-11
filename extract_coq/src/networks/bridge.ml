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

let string_of_json_float f =
  let s = Printf.sprintf "%.17g" f in
  if String.equal s "-nan" || String.equal s "nan" then failwith "nan is not valid JSON"
  else if String.equal s "inf" || String.equal s "-inf" then
    failwith "infinity is not valid JSON"
  else s

let string_of_json_list string_of_value xs =
  "[" ^ String.concat "," (List.map string_of_value xs) ^ "]"

let string_of_json_float_list = string_of_json_list string_of_json_float

let string_of_json_int_list = string_of_json_list string_of_int

let string_of_json_int_matrix = string_of_json_list string_of_json_int_list

let with_temp_json_arg (payload : string) (k : string -> 'a) : 'a =
  (* Keep command-line args small to avoid E2BIG on large Hamiltonians. *)
  let path = Filename.temp_file "qblue_api_" ".json" in
  let oc = open_out_bin path in
  output_string oc payload;
  close_out oc;
  try
    let result = k ("@" ^ path) in
    Sys.remove path;
    result
  with exn ->
    (try Sys.remove path with _ -> ());
    raise exn

let skip_ws s idx =
  while
    !idx < String.length s
    &&
    match s.[!idx] with
    | ' ' | '\n' | '\r' | '\t' -> true
    | _ -> false
  do
    incr idx
  done

let expect_char s idx c =
  skip_ws s idx;
  if !idx >= String.length s || s.[!idx] <> c then
    failwith (Printf.sprintf "invalid JSON: expected '%c'" c);
  incr idx

let parse_json_float s idx =
  skip_ws s idx;
  let start = !idx in
  while
    !idx < String.length s
    &&
    match s.[!idx] with
    | '0' .. '9' | '-' | '+' | '.' | 'e' | 'E' -> true
    | _ -> false
  do
    incr idx
  done;
  if !idx = start then failwith "invalid JSON: expected number";
  float_of_string (String.sub s start (!idx - start))

let parse_json_float_list s idx =
  expect_char s idx '[';
  skip_ws s idx;
  if !idx < String.length s && s.[!idx] = ']' then (
    incr idx;
    [])
  else
    let rec loop acc =
      let value = parse_json_float s idx in
      skip_ws s idx;
      if !idx < String.length s && s.[!idx] = ',' then (
        incr idx;
        loop (value :: acc))
      else (
        expect_char s idx ']';
        List.rev (value :: acc))
    in
    loop []

let parse_json_float_matrix s =
  let idx = ref 0 in
  expect_char s idx '[';
  skip_ws s idx;
  let rows =
    if !idx < String.length s && s.[!idx] = ']' then (
      incr idx;
      [])
    else
      let rec loop acc =
        let row = parse_json_float_list s idx in
        skip_ws s idx;
        if !idx < String.length s && s.[!idx] = ',' then (
          incr idx;
          loop (row :: acc))
        else (
          expect_char s idx ']';
          List.rev (row :: acc))
      in
      loop []
  in
  skip_ws s idx;
  if !idx <> String.length s then failwith "invalid JSON: trailing data";
  rows

let get_matrix_pgc list_coef cnot_matrix singleq_matrix =
  let list_coef_json = string_of_json_float_list list_coef in
  let cnot_matrix_json = string_of_json_int_matrix cnot_matrix in
  let singleq_matrix_json =
    match singleq_matrix with
    | Some m -> Some (string_of_json_int_matrix m)
    | None -> None
  in
  let python_bin =
    match find_python_path "python3" with
    | Some p -> p
    | None -> "/usr/bin/python3"
  in
  let api_path = find_api_path () in
  with_temp_json_arg list_coef_json (fun list_coef_arg ->
      with_temp_json_arg cnot_matrix_json (fun cnot_matrix_arg ->
          let run singleq_arg_opt =
            let extra_args =
              match singleq_arg_opt with
              | Some s -> [| list_coef_arg; cnot_matrix_arg; s |]
              | None -> [| list_coef_arg; cnot_matrix_arg |]
            in
            let py_args =
              Array.append
                [| python_bin; api_path; "genmat_gate_cancellation" |]
                extra_args
            in
            let ic = Unix.open_process_args_in python_bin py_args in
            let output = read_all ic in
            match Unix.close_process_in ic with
            | Unix.WEXITED 0 -> parse_json_float_matrix (String.trim output)
            | Unix.WEXITED code ->
                failwith (Printf.sprintf "python api failed with exit code %d" code)
            | Unix.WSIGNALED signal ->
                failwith (Printf.sprintf "python api killed by signal %d" signal)
            | Unix.WSTOPPED signal ->
                failwith (Printf.sprintf "python api stopped by signal %d" signal)
          in
          match singleq_matrix_json with
          | Some s -> with_temp_json_arg s (fun s_arg -> run (Some s_arg))
          | None -> run None))
