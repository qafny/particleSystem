open Main

let string_of_complex (re, im) =
  Printf.sprintf "(%f + %fi)" re im

let () = 
  Printf.printf "C1 = %s\n" (string_of_complex c1)


(* test lowprog *)
(* let string_of_paulimat = function
  | paulix -> "X"
  | pauliy -> "Y"
  | pauliz -> "Z"
  | paulii -> "I"

let string_of_lowprog_ten (amp, len, f) =
  (* build "X ⊗ Y ⊗ Z ..." using the function f *)
  let buf = Buffer.create 32 in
  for i = 0 to len - 1 do
    if i > 0 then Buffer.add_string buf " ⊗ ";
    Buffer.add_string buf (string_of_paulimat (f i))
  done;
  let paulis = Buffer.contents buf in
  Printf.sprintf "%s · (%s)" (string_of_complex amp) paulis

let string_of_lowprog (lp : lowprog) =
  let rec aux = function
    | [] -> ""
    | [g] -> string_of_lowprog_ten g
    | g :: gs ->
        string_of_lowprog_ten g ^ " ; " ^ aux gs
  in
  "[" ^ aux lp ^ "]"
  
let () = 
  Printf.printf "lowp = %s\n" (string_of_lowprog lowp)
 *) 


