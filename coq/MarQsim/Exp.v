From Coq Require Import List String.
Require Import Overall Varying Spectra CompileTime.
Import ListNotations.

Inductive Experiment : Type := EOverall | EVarying | ESpectra | EEvol | ETime.

(* In Python exp.py dispatches shell command strings; in Coq we model the dispatch target. *)
Definition dispatch_target (e : Experiment) : string :=
  match e with
  | EOverall => "overall"
  | EVarying => "varying"
  | ESpectra => "spectra"
  | EEvol => "evol"
  | ETime => "time"
  end.
