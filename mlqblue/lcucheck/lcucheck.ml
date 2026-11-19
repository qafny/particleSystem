(* Dump an extracted LCU circuit as a gate list for scripts/check_lcu.py, or
   check that its resource pieces add up to the full circuit.
   usage: lcucheck.exe <ham.txt> <taylor|qwalk|qsp|qsvt> <err> <t> <out.txt> [counts] *)
open QBlueSyntax

let read_terms f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let re = Str.regexp "\\([+-]\\)[ \t]*\\([0-9.eE+-]+\\)[ \t]*\\*[ \t]*\\([IXYZ]+\\)" in
  let rec go pos acc =
    match Str.search_forward re s pos with
    | exception Not_found -> List.rev acc
    | _ ->
      let c = float_of_string (Str.matched_group 2 s) in
      let c = if Str.matched_group 1 s = "-" then -. c else c in
      go (Str.match_end ()) ((c, Str.matched_group 3 s) :: acc)
  in
  go 0 []

let to_lowprog terms : lowprog =
  List.map (fun (c, p) ->
      let f i =
        if i >= String.length p then Coq_paulii
        else match p.[i] with
          | 'X' -> Coq_paulix | 'Y' -> Coq_pauliy | 'Z' -> Coq_pauliz | _ -> Coq_paulii in
      ((c, 0.0), f)) terms

let () =
  let file = Sys.argv.(1) and meth = Sys.argv.(2) in
  let err = float_of_string Sys.argv.(3) and t = float_of_string Sys.argv.(4) in
  let terms = read_terms file in
  let nq = String.length (snd (List.hd terms)) in
  let lp = to_lowprog terms in
  let build = match meth with
    | "taylor" -> QBlueTTS_v4.taylor_circuit
    | "qwalk" -> QBlueQuantumWalk.qwalk_circuit
    | "qsp" -> QBlueQubitization.qsp_circuit
    | "qsvt" -> QBlueQSVT.qsvt_circuit
    | _ -> failwith "method" in
  let gates = build err t nq lp in
  let oc = open_out Sys.argv.(5) in
  let open ExtractionGateSet in
  let rec emit = function
    | Coq_useq (a, b) -> emit a; emit b
    | Coq_uapp (_, U_X, [q]) -> Printf.fprintf oc "x %d\n" q
    | Coq_uapp (_, U_H, [q]) -> Printf.fprintf oc "h %d\n" q
    | Coq_uapp (_, U_U1 a, [q]) -> Printf.fprintf oc "u1 %.17g %d\n" a q
    | Coq_uapp (_, U_U3 (a, b, c), [q]) -> Printf.fprintf oc "u3 %.17g %.17g %.17g %d\n" a b c q
    | Coq_uapp (_, U_CX, [a; b]) -> Printf.fprintf oc "cx %d %d\n" a b
    | Coq_uapp (_, U_CCX, [a; b; c]) -> Printf.fprintf oc "ccx %d %d %d\n" a b c
    | _ -> failwith "unexpected gate" in
  List.iter emit gates;
  close_out oc;
  Printf.printf "%d gates\n" (List.length gates)

(* consistency: raw counts of the full circuit = sum of pieces x multiplicity *)
let () =
  if Array.length Sys.argv > 6 && Sys.argv.(6) = "counts" then begin
    let file = Sys.argv.(1) and meth = Sys.argv.(2) in
    let err = float_of_string Sys.argv.(3) and t = float_of_string Sys.argv.(4) in
    let terms = read_terms file in
    let nq = String.length (snd (List.hd terms)) in
    let lp = to_lowprog terms in
    let full, pieces = match meth with
      | "taylor" -> QBlueTTS_v4.taylor_circuit, QBlueTTS_v4.taylor_pieces
      | "qwalk" -> QBlueQuantumWalk.qwalk_circuit, QBlueQuantumWalk.qwalk_pieces
      | "qsp" -> QBlueQubitization.qsp_circuit, QBlueQubitization.qsp_pieces
      | _ -> QBlueQSVT.qsvt_circuit, QBlueQSVT.qsvt_pieces in
    let (((nqt, _), _), parts) = pieces err t nq lp in
    let raw l =
      let rz = QBlueSynthDigital.ibmdigi_to_rzq_a2a nqt (QBlueQuantumWalk.to_ucom l) in
      (Main.count_total nqt rz, Main.count_CX nqt rz) in
    let (ft, fc) = raw (full err t nq lp) in
    let (pt, pc) = List.fold_left (fun (a, b) (m, p) -> let (x, y) = raw p in (a + m * x, b + m * y)) (0, 0) parts in
    Printf.printf "%s: full circuit raw total=%d cx=%d | pieces total=%d cx=%d | %s\n" meth ft fc pt pc
      (if ft = pt && fc = pc then "MATCH" else "MISMATCH")
  end
