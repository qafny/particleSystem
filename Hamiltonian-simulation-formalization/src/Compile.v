(** -- Compile.v -- **)
(* Contains our main function to extract to OCaml *)

Require Import String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.
Require Import Qasm.
Require Import Trotterize.
Require Import Decimal.

Open Scope list_scope.
Open Scope string_scope.

Import ListNotations.

(* Placeholder. TODO replace with working parser *)
Definition parseProgram (program_text : string) : H_Program := makeHProg [] [].

(* The compile pipeline: parse, AST transform, and then print. *)
Definition compile (program_text : string) (nSlices_text : string) :=
    let nSlices := Nat.of_uint (
        match (NilEmpty.uint_of_string nSlices_text) with
        | Some x => x
        | None => Nil
        end
    ) in
    let program := parseProgram program_text in
    let qasm := (trotterize program nSlices).(output) in
    print_qasm_program qasm.

(**
 * TODO it may make sense to state a main theorem here,
 * by combining our AST transform correctness with parsing/printing?
 *)

Extraction "extracted/compile_coq.ml" compile.
