open Parser
open Lexer
open Revert_to_lowprog

let () =
  let input =
    if Array.length Sys.argv >= 2 then Sys.argv.(1)
    else "+1.0*X+2.0*Y"
  in
  let lexbuf = Lexing.from_string input in
  try
    let prog = Parser.program Lexer.token lexbuf in
    (* Print exactly for this case: 1 pauli per term *)
    Printf.printf "Parsed as: %s\n" (Revert_to_lowprog.string_of_lowprog ~n:100 prog;
    );
  with
  | Parser.Error ->
      Printf.eprintf "Parser error near offset %d (lexeme=%S)\n"
        (Lexing.lexeme_start lexbuf) (Lexing.lexeme lexbuf)



