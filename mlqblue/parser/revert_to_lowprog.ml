open Syntax

let string_of_paulimat = function
  | Coq_paulix -> "X"
  | Coq_pauliy -> "Y"
  | Coq_pauliz -> "Z"
  | Coq_paulii -> "I"

(* show first [n] Paulis of the map f : int -> paulimat *)
let paulis_prefix n (f : int -> paulimat) : string =
  let buf = Buffer.create n in
  for i = 0 to n - 1 do
    Buffer.add_string buf (string_of_paulimat (f i))
  done;
  Buffer.contents buf

let string_of_term ?(n=8) (((re, im), f) : lowprog_ten) : string =
  Printf.sprintf "+%g*%s" re (paulis_prefix n f)

let string_of_lowprog ?(n=8) (p : lowprog) : string =
  String.concat "" (List.map (string_of_term ~n) p)

