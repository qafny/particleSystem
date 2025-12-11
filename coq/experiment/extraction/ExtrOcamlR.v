Require Coq.extraction.Extraction.
Require Export Reals.
Require Import QBlue.QBlueUtility.

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
(* Extract Inlined Constant IZR => "float_of_int".
Extract Inlined Constant INR => "float_of_int".
Extract Inlined Constant IZR => "Z.to_float".
*)
Extract Inlined Constant IZR =>
"(fun z -> Z.to_float z)".

Extract Inlined Constant INR =>
"(fun n -> Z.to_float n)".

Extract Inlined Constant Rceil_Z =>
  "fun x -> Z.of_int (int_of_float (ceil x))".

(* Extracting the following to dummy values to supress warnings *)
Extract Constant ClassicalDedekindReals.sig_forall_dec  => "failwith ""Invalid extracted value"" ".
Extract Constant ClassicalDedekindReals.DRealRepr  => "failwith ""Invalid extracted value"" ".
