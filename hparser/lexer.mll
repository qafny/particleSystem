{

open Common
}

let numeric = ['0' - '9']

rule token = parse
        | [' ' '\t' '\n'] { token lexbuf }  (* skip over whitespace *)
        | eof             { EOF }
          (* binary operators *)
        | "_"    { UNDER }
        | "+"    { PLUS }
        | "*"   { TIMES }
        | "-"    { MINUS }
        | "("    {LPAR}
        | ")"    {RPAR}
        | numeric   { NAT (int_of_string s) }
        | ('-')? numeric+ '.'(numeric*) as s { FLOAT (float_of_string s) }

{(* do not modify this function: *)
let lextest s = token (Lexing.from_string s)

let get_all_tokens s =
     let b = Lexing.from_string (s^"\n") in
     let rec g () =
     match token b with EOF -> []
     | t -> t :: g () in
     g ()
     
let get_all_token_options s =
  let b = Lexing.from_string (s^"\n") in
  let rec g () =
    match (try Some (token b) with _ -> None) with Some EOF -> []
      | None -> [None]
      | t -> t :: g () in
  g ()

 }

