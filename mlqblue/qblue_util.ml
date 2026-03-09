
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

(* Maybe needed to check invalid lowprog in the future *)
let is_finite x =
  match classify_float x with
  | FP_normal | FP_subnormal | FP_zero -> true
  | FP_infinite | FP_nan -> false

let dbg fmt =
  Printf.kfprintf (fun oc -> output_char oc '\n'; flush oc) stderr ("[DBG] " ^^ fmt)



