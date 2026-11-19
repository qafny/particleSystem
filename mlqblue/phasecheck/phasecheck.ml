(* Solve the QSVT phases of every QSVT job (path 8) exactly as qsvt_circuit
   does, and print them for scripts/check_qsvt_phases.py to verify.
   qsvt_pieces, which the benchmark counts gates from, never computes phases
   (gate counts do not depend on them), so this is the check that every
   benchmark circuit has valid phases.
   usage: phasecheck.exe <job csv> <data dir> [lbfgs]   (one JSON line per polynomial)
   With "lbfgs", also prints the phases of Ian's Dong-Lin L-BFGS alone
   (before qsvt_phases' Newton refinement), to show how far it gets. *)
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

let pr l = "[" ^ String.concat "," (List.map (Printf.sprintf "%.17g") l) ^ "]"

let () =
  let jobs = Sys.argv.(1) and data = Sys.argv.(2) in
  let lbfgs = Array.length Sys.argv > 3 && Sys.argv.(3) = "lbfgs" in
  let ic = open_in jobs in
  ignore (input_line ic);                                   (* header *)
  let cache = Hashtbl.create 64 in
  (try while true do
    match String.split_on_char ',' (String.trim (input_line ic)) with
    | [file; err; t; "8"] ->
      let err = float_of_string err and t = float_of_string t in
      let lp =
        match Hashtbl.find_opt cache file with
        | Some lp -> lp
        | None ->
          let lp = QBlueQuantumWalk.lcu_terms (to_lowprog (read_terms (Filename.concat data file))) in
          Hashtbl.add cache file lp; lp in
      (* qsvt_circuit: r segments, tau = lambda t / r, eta = delta = err / (8 r) *)
      let r = QBlueQSVT.qsvt_segments lp t in
      let tau = QBlueQuantumWalk.lcu_lambda lp *. t /. float_of_int r in
      let e = err /. (8.0 *. float_of_int r) in
      let k = QBlueQuantumWalk.findK_qwalk tau e in
      let dc = if k mod 2 = 0 then k else k + 1 in
      let sc l = List.map (fun c -> (1.0 -. e) *. c) l in
      List.iter (fun (lab, c, p) ->
          let t0 = Unix.gettimeofday () in
          let ph = QBlueQSVT.qsvt_phases c p in
          let secs = Unix.gettimeofday () -. t0 in
          let extra =
            if not lbfgs then ""
            else
              let t1 = Unix.gettimeofday () in
              let lb = QBlueQSPCore.full_phases (QBlueQSVT_updateQSP.donglin_reduced c p)
                         (QBlueQSPCore.qsp_degree c p) in
              Printf.sprintf ",\"lbfgs_seconds\":%.4f,\"lbfgs_phases\":%s" (Unix.gettimeofday () -. t1) (pr lb) in
          Printf.printf
            "{\"file_name\":%S,\"error\":%.17g,\"time\":%.17g,\"segments\":%d,\"tau\":%.17g,\"eta\":%.17g,\"target\":%S,\"seconds\":%.4f,\"cheb\":%s,\"phases\":%s%s}\n%!"
            file err t r tau e lab secs (pr c) (pr ph) extra)
        [ ("cos", sc (QBlueQSVT.cheb_cos tau dc), 0); ("sin", sc (QBlueQSVT.cheb_sin tau (dc + 1)), 1) ]
    | _ -> ()
  done with End_of_file -> ());
  close_in ic
