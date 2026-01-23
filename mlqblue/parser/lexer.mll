{
open Parser
}

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let letter =['a' - 'z' 'A' - 'Z' '_']
let hex = ['0' - '9' 'a' - 'f']
let ident_char = letter | numeric | '_' | '\''
let string_char = ident_char | ' ' | '~' | '`' | '!' | '@' | '#' | '$' | '%' | '^' | '&'
  | '*' | '(' | ')' | '-' | '+' | '=' | '{' | '[' | '}' | ']'
  | '|' | ':' | ';' | '<' | ',' | '>' | '.' | '?' | '/' 

let open_comment = "(*"
let close_comment = "*)"
let whitespace = [' ' '\t' '\n']

rule token = parse
        | [' ' '\t' '\n'] { token lexbuf }  (* skip over whitespace *)
        | eof             { EOF }
          (* binary operators *)
        | "+"    { PLUS }
        | "*"   { TIMES }
        | "X"    { XPau }
        | "Y"    { YPau }
        | "Z"    { ZPau }
        | "I"   { IPau }
        | numeric+'.'(numeric*) as s { FLOAT (float_of_string s) }

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

