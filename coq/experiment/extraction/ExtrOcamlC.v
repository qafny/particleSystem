Require Coq.extraction.Extraction.
Require Import QuantumLib.Complex.

(* Custom extraction from R -> OCaml float. *)
Extract Inlined Constant C => "float * float".
Extract Inlined Constant RtoC => "(fun x -> (x, 0.0))".
Extract Inlined Constant Ci => "(0.0, 1.0)".

Extract Inlined Constant Cmult => "(fun (a1, a2) (b1, b2) -> (a1 *. b1 -. a2 *. b2, a1 *. b2 +. a2 *. b1))".
Extract Inlined Constant Complex.Copp => "(fun (a, b) -> (-. a, -. b))".



