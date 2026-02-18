From Coq Require Import List String QArith.
Require Import Marqsim.
Import ListNotations.
Open Scope Q_scope.

Record OverallArgs : Type := {
  exp_path : string;
  file_name : string;
  lam_list : list (list Q);
  epsilon_list : list Q;
  execute_time : Q;
  sampling_time : nat;
  h_sum : Q
}.

Definition run_overall (args : OverallArgs) :=
  operation
    (lam_list args)
    (file_name args)
    (exp_path args)
    (execute_time args)
    (sampling_time args)
    (epsilon_list args).
