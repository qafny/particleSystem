From Coq Require Import Extraction.
Require Import Reals. 
Require Import Psatz.
Require Import List. 


Require Import QBlue.Main.
Require Coq.extraction.ExtrOcamlBasic.

Require Export Reals.
Require Import QBlue.QBlueUtility.
Require Import QuantumLib.Complex.

(* A few common list functions *)
(* Extract Constant length => "(fun l -> Z.of_int (List.length l))". *)


(* Don’t let Coq define its own List module in OCaml *)
Extraction Blacklist List.
Extract Inlined Constant List.length => "(fun l -> (Stdlib.List.length l))".
Extract Inlined Constant app => " (@) ".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant List.map => "List.map".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant List.tl => "List.tl".
Extract Inlined Constant List.hd_error => "(fun l -> List.nth_opt l 0)".



(* Custom extraction from R -> OCaml float. *)
Definition R2 : R := 2.
Definition R4 : R := 4.
Definition R8 : R := 8.
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".

Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Ropp => "((-.) 0.0)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "( /. )".
Extract Inlined Constant sqrt => "sqrt".
Extract Inlined Constant pow => "(fun a b -> a ** Z.to_float b)".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "atan".
Extract Inlined Constant acos => "acos".
Extract Inlined Constant PI => "Float.pi".

(*Chagned by Teddy*)
Extract Inlined Constant INR => "float_of_int".
(*
Extract Inlined Constant IZR => "(fun n -> Z.to_float n)".
*)


(* Extracting the following to dummy values to supress warnings *)
Extract Constant ClassicalDedekindReals.sig_forall_dec  => "failwith ""Invalid extracted value"" ".
Extract Constant ClassicalDedekindReals.DRealRepr  => "failwith ""Invalid extracted value"" ".


(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.
Extract Inductive nat => int [ "0" "succ" ] (* fix to bug in current lib *)
  "(fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))".
Extract Inlined Constant Init.Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.leb => "(<=)".
Extract Inlined Constant Init.Nat.ltb => "(<)".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Init.Nat.sub => "(fun x y -> max 0 (x-y))".
(* Extract Inlined Constant C38168 => "38168".  manually extracting large constants *)

(*
Extract Inlined Constant N.of_nat => "(fun x -> x)". (* id *)
*)

(* Extract Constant id_nat => "fun x : int -> x".  add type annotation *) 


(* Custom extraction from R -> OCaml float. *)
Extract Inlined Constant C => "float * float".
Extract Inlined Constant RtoC => "(fun x -> (x, 0.0))".
Extract Inlined Constant Ci => "(0.0, 1.0)".

Extract Inlined Constant Cmult => "(fun (a1, a2) (b1, b2) -> (a1 *. b1 -. a2 *. b2, a1 *. b2 +. a2 *. b1))".
Extract Inlined Constant Complex.Copp => "(fun (a, b) -> (-. a, -. b))".

Locate ceilR_N.

Set Extraction Optimize.
Separate Extraction Main.lowp.




