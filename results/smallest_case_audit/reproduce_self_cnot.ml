(* Calls the existing built QBlue parser and synthesis. No QASM conversion. *)
open QBlueSyntax
open ExtractionGateSet

let rec self_cnots = function
  | Coq_useq (a, b) -> self_cnots a @ self_cnots b
  | Coq_uapp (_, U_CX, [a; b]) when a = b -> [a]
  | _ -> []

let () =
  if Array.length Sys.argv <> 2 then failwith "Usage: reproduce_self_cnot INPUT.txt";
  let path = Sys.argv.(1) in
  let ic = open_in path in
  let lp = Parserlib.Parser.program Parserlib.Lexer.token (Lexing.from_channel ic) in
  close_in ic;
  let ic = open_in path in
  let rec lines acc = try let s = input_line ic in lines (s :: acc) with End_of_file -> List.rev acc in
  let source = lines [] in close_in ic;
  let first = List.find (fun s -> String.contains s '*') source in
  let n = String.length (String.trim (List.nth (String.split_on_char '*' first) 1)) in
  let total = ref 0 and affected = ref 0 in
  Printf.printf "Input: %s\nParsed by QBlue: %d terms, %d qubits\n" path (List.length lp) n;
  List.iteri (fun i ((_, f) as term) ->
    let bad = self_cnots (QBlueSynthDigital.synth_digital_ibm 0.7854 n [term]) in
    if bad <> [] then begin
      incr affected; total := !total + List.length bad;
      if !affected <= 3 then begin
        let label = String.init n (fun j -> match f j with
          | Coq_paulii -> 'I' | Coq_paulix -> 'X' | Coq_pauliy -> 'Y' | Coq_pauliz -> 'Z') in
        Printf.printf "Term %d (%s):\n" (i+1) label;
        List.iter (fun q -> Printf.printf "  CX(control=%d, target=%d)\n" q q) bad
      end
    end) lp;
  Printf.printf "Single pass: %d self-CNOTs in %d of %d terms\n" !total !affected (List.length lp);
  let block = QBlueCompile.translate_lowp2circ_2ndTrotter 0.1 0.7854 lp n (QBlueSynthDigital.ibmdigi_to_rzq n) in
  let count = List.fold_left (fun acc -> function
    | UnitaryListRepresentation.App2 (FullGateSet.FullGateSet.U_CX, a, b) when a = b -> acc + 1
    | _ -> acc) 0 block in
  Printf.printf "QBlue production path-2 pre-optimization block: %d self-CNOTs\n" count
