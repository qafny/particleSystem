open Parser
open Lexer
open Revert_to_lowprog

let () =
  let input = open_in "JW_benzene_sto3g_42_electrons_72_spin_orbitals_Hamiltonian_368021_paulis.txt"
  in
  try 
    while true do
      let line = input_line input in
      let lexbuf = Lexing.from_string line in
      try
       let prog = Parser.program Lexer.token lexbuf in
    (* Print exactly for this case: 1 pauli per term *)
       ()
       with
      | Parser.Error ->
          close_in input; Printf.eprintf "Parser error near offset\n"
         done
   with End_of_file -> close_in input; Printf.printf "good\n"
