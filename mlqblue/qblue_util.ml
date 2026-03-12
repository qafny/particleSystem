
exception Parse_timeout of int

let with_timeout (seconds : int) (f : unit -> 'a) : 'a =
  if seconds <= 0 then f ()
  else
    let old_handler =
      Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise (Parse_timeout seconds)))
    in
    ignore (Unix.alarm seconds);
    try
      let result = f () in
      ignore (Unix.alarm 0);
      ignore (Sys.signal Sys.sigalrm old_handler);
      result
    with exn ->
      ignore (Unix.alarm 0);
      ignore (Sys.signal Sys.sigalrm old_handler);
      raise exn

let getenv_int (name : string) (default : int) : int =
  match Sys.getenv_opt name with
  | None -> default
  | Some raw ->
      let value = String.trim raw in
      if value = "" then default
      else
        try int_of_string value with
        | Failure _ ->
            Printf.eprintf "[DBG] Ignoring invalid integer env %s=%S; using default %d\n%!" name raw default;
            default

(* Maybe needed to check invalid lowprog in the future *)
let is_finite x =
  match classify_float x with
  | FP_normal | FP_subnormal | FP_zero -> true
  | FP_infinite | FP_nan -> false

let dbg fmt =
  Printf.kfprintf (fun oc -> output_char oc '\n'; flush oc) stderr ("[DBG] " ^^ fmt)


