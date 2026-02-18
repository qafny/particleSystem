From Coq Require Import List String QArith.
Require Import Marqsim.
Import ListNotations.
Open Scope Q_scope.

Record CompileTimeArgs : Type := {
  exp_path : string;
  file_name : string;
  lam_list : list (list Q);
  epsilon_list : list Q;
  execute_time : Q;
  sampling_time : nat
}.

Definition run_compile_time (args : CompileTimeArgs) :=
  compilation_time_operation
    (lam_list args)
    (file_name args)
    (exp_path args)
    (execute_time args)
    (sampling_time args)
    (epsilon_list args).
