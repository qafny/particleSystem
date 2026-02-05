

(* Maybe needed to check invalid lowprog in the future *)
let is_finite x =
  match classify_float x with
  | FP_normal | FP_subnormal | FP_zero -> true
  | FP_infinite | FP_nan -> false

let dbg fmt =
  Printf.kfprintf (fun oc -> output_char oc '\n'; flush oc) stderr ("[DBG] " ^^ fmt)



