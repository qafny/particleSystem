From Coq Require Import List String ZArith QArith Reals.
From Coq Require Import Sorting.Permutation.
Require Import NetworkX.
Import ListNotations.

Open Scope Q_scope.

Inductive Pauli : Type := PI | PX | PY | PZ.

Record PauliTerm : Type := {
  ops : list Pauli;
  coeff : Q
}.

Definition Hamiltonian := list PauliTerm.
Definition CostMatrix := list (list nat).
Definition ProbMatrix := list (list Q).

Definition nth_default {A : Type} (d : A) (xs : list A) (i : nat) : A := nth i xs d.

Definition matrix_lookup_nat (m : CostMatrix) (i j : nat) : nat :=
  nth_default 0%nat (nth_default [] m i) j.

Definition qabs (x : Q) : Q := if Qlt_le_dec x 0 then -x else x.

Definition pauli_eqb (a b : Pauli) : bool :=
  match a, b with
  | PI, PI | PX, PX | PY, PY | PZ, PZ => true
  | _, _ => false
  end.

Definition is_I (p : Pauli) : bool := pauli_eqb p PI.
Definition is_XY (p : Pauli) : bool := orb (pauli_eqb p PX) (pauli_eqb p PY).

Definition term_weight (t : PauliTerm) : Q := qabs (coeff t).

Definition lambda_sum (h : Hamiltonian) : Q :=
  fold_left Qplus (map term_weight h) 0%Q.

Definition normalize_probs (h : Hamiltonian) : list Q :=
  let lam := lambda_sum h in
  if Qeq_bool lam 0
  then repeat 0%Q (List.length h)
  else map (fun t => (term_weight t) / lam) h.

Definition get_markov_0 (input_pauli : Hamiltonian) : ProbMatrix :=
  let pro := normalize_probs input_pauli in
  repeat pro (List.length input_pauli).

Fixpoint cnot_cost_ops (a b : list Pauli) : nat :=
  match a, b with
  | x :: xs, y :: ys =>
      let base := if pauli_eqb x y then 0%nat else 1%nat in
      let extra := if andb (negb (is_I x)) (negb (is_I y))
                   then if pauli_eqb x y then 0%nat else 1%nat
                   else 0%nat in
      base + extra + cnot_cost_ops xs ys
  | _, _ => 0%nat
  end.

Fixpoint xy_count (xs : list Pauli) : nat :=
  match xs with
  | [] => 0%nat
  | x :: tl => (if is_XY x then 1%nat else 0%nat) + xy_count tl
  end.

Fixpoint xy_overlap (a b : list Pauli) : nat :=
  match a, b with
  | x :: xs, y :: ys =>
      (if andb (pauli_eqb x y) (is_XY x) then 1%nat else 0%nat) + xy_overlap xs ys
  | _, _ => 0%nat
  end.

Definition single_q_cost_ops (a b : list Pauli) : nat :=
  xy_count a + xy_count b - 2 * xy_overlap a b.

Definition row_costs (f : list Pauli -> list Pauli -> nat) (row : PauliTerm) (all : Hamiltonian) : list nat :=
  map (fun t => f (ops row) (ops t)) all.

Definition get_CNOT_matrix (input_pauli : Hamiltonian) : CostMatrix :=
  map (fun row => row_costs cnot_cost_ops row input_pauli) input_pauli.

Definition get_single_q_matrix (input_pauli : Hamiltonian) : CostMatrix :=
  map (fun row => row_costs single_q_cost_ops row input_pauli) input_pauli.

(* Bridge from Coq rationals/costs to integer capacities and stochastic perturbations. *)
Definition z_to_Q (z : Z) : Q := inject_Z z.

Definition z_round_half_up (num den : Z) : Z :=
  Z.div (num + Z.div den 2) den.

(* Matches Python: int(abs(coeff) * 10000 + 0.5). *)
Definition scaled_capacity (q : Q) : Z :=
  let a := qabs q in
  let num := (Qnum a * 10000)%Z in
  let den := Z.pos (Qden a) in
  z_round_half_up num den.

Parameter perturb_weight : nat -> nat -> Z.

Definition add_supply_nodes (g : DiGraph) (sum_hj_10 : Z) : DiGraph :=
  set_node_demand (set_node_demand g NSrc (- sum_hj_10)) NSink sum_hj_10.

Definition add_terminal_edges (g : DiGraph) (input_pauli : Hamiltonian) : DiGraph :=
  fold_left
    (fun acc i =>
       let t := nth_default {| ops := []; coeff := 0%Q |} input_pauli i in
       let cap := scaled_capacity (coeff t) in
       add_edges_from acc
         [{| src := NSrc; dst := NB i; attr := {| capacity := cap; weight := 0 |} |};
          {| src := NC i; dst := NSink; attr := {| capacity := cap; weight := 0 |} |}])
    (seq 0 (List.length input_pauli))
    g.

Definition add_transition_edges
    (g : DiGraph)
    (input_pauli : Hamiltonian)
    (cnot single_q : CostMatrix)
    (with_perturb : bool) : DiGraph :=
  fold_left
    (fun acc ij =>
       let i := fst ij in
       let j := snd ij in
       if Nat.eqb i j then acc else
       let t := nth_default {| ops := []; coeff := 0%Q |} input_pauli i in
       let cap := scaled_capacity (coeff t) in
       let base_cost :=
         Z.of_nat (matrix_lookup_nat cnot i j + matrix_lookup_nat single_q i j) in
       let w := if with_perturb then (base_cost + perturb_weight i j)%Z else base_cost in
       add_edge acc {| src := NB i; dst := NC j; attr := {| capacity := cap; weight := w |} |})
    (List.concat
      (map (fun i => map (fun j => (i, j)) (seq 0 (List.length input_pauli)))
           (seq 0 (List.length input_pauli))))
    g.

Definition build_flow_graph
    (input_pauli : Hamiltonian)
    (cnot single_q : CostMatrix)
    (with_perturb : bool) : DiGraph :=
  let sum_hj_10 :=
    fold_left Z.add (map (fun t => scaled_capacity (coeff t)) input_pauli) 0%Z in
  let g0 := add_supply_nodes empty_graph sum_hj_10 in
  let g1 := add_terminal_edges g0 input_pauli in
  add_transition_edges g1 input_pauli cnot single_q with_perturb.

Definition flow_bc (f : FlowDict) (i j : nat) : Z :=
  flow_lookup f (NB i) (NC j).

Definition safe_ratio_Q (num den : Z) : Q :=
  if Z.eqb den 0%Z then 0%Q else (z_to_Q num / z_to_Q den)%Q.

Definition row_from_flow
    (input_pauli : Hamiltonian)
    (f : FlowDict)
    (i n : nat) : list Q :=
  let t := nth_default {| ops := []; coeff := 0%Q |} input_pauli i in
  let cap := scaled_capacity (coeff t) in
  map (fun j => safe_ratio_Q (flow_bc f i j) cap) (seq 0 n).

Definition flow_to_prob_matrix (input_pauli : Hamiltonian) (f : FlowDict) : ProbMatrix :=
  let n := List.length input_pauli in
  map (fun i => row_from_flow input_pauli f i n) (seq 0 n).

Definition get_markov_1 (input_pauli : Hamiltonian) : ProbMatrix :=
  let cnot := get_CNOT_matrix input_pauli in
  let single_q := get_single_q_matrix input_pauli in
  let g := build_flow_graph input_pauli cnot single_q false in
  let '(_, f) := network_simplex g in
  flow_to_prob_matrix input_pauli f.

Definition get_markov_2 (input_pauli : Hamiltonian) : ProbMatrix :=
  let cnot := get_CNOT_matrix input_pauli in
  let single_q := get_single_q_matrix input_pauli in
  let g := build_flow_graph input_pauli cnot single_q true in
  let '(_, f) := network_simplex g in
  flow_to_prob_matrix input_pauli f.

Definition start_end_costs (input_pauli : Hamiltonian) (idx : nat) : nat * nat :=
  let t := nth_default {| ops := []; coeff := 0%Q |} input_pauli idx in
  (List.length (filter (fun p => negb (is_I p)) (ops t)), xy_count (ops t)).

Fixpoint transition_costs_from
    (cnot single_q : CostMatrix)
    (prev : nat)
    (rest : list nat)
    (acc_cnot acc_single : nat) {struct rest} : nat * nat :=
  match rest with
  | [] => (acc_cnot, acc_single)
  | b :: tl =>
      transition_costs_from cnot single_q b tl
        (acc_cnot + matrix_lookup_nat cnot prev b)
        (acc_single + matrix_lookup_nat single_q prev b)
  end.

Definition transition_costs
    (cnot single_q : CostMatrix)
    (samples : list nat)
    (acc_cnot acc_single : nat) : nat * nat :=
  match samples with
  | [] => (acc_cnot, acc_single)
  | first :: rest => transition_costs_from cnot single_q first rest acc_cnot acc_single
  end.

Record CompileResult : Type := {
  cnot_count : nat;
  single_q_count : nat;
  sampled_indices : list nat
}.

(* Coq is pure: caller provides sampled indices instead of RNG side-effects. *)
Definition random_compiler_2
    (input_pauli : Hamiltonian)
    (_epsilon t : Q)
    (cnot single_q : CostMatrix)
    (_P_mix : ProbMatrix)
    (_pro : list Q)
    (samples : list nat) : CompileResult :=
  match samples with
  | [] => {| cnot_count := 0%nat; single_q_count := 0%nat; sampled_indices := [] |}
  | first :: _ =>
      let '(body_cnot, body_single) := transition_costs cnot single_q samples 0%nat 0%nat in
      let '(start_cnot, start_single) := start_end_costs input_pauli first in
      let '(end_cnot, end_single) :=
        start_end_costs input_pauli (nth_default first samples (List.length samples - 1%nat)) in
      {| cnot_count := body_cnot + start_cnot + end_cnot;
         single_q_count := body_single + start_single + end_single + List.length samples;
         sampled_indices := samples |}
  end.

(* random_compiler_1 additionally computes state-vector accuracy in Python. *)
Parameter random_compiler_1 :
  Hamiltonian -> Q -> Q -> CostMatrix -> CostMatrix -> ProbMatrix -> list Q -> list nat -> CompileResult.

Fixpoint inc_count (k : nat) (m : list (nat * nat)) : list (nat * nat) :=
  match m with
  | [] => [(k, 1%nat)]
  | (x, c) :: tl =>
      if Nat.eqb x k then (x, S c) :: tl else (x, c) :: inc_count k tl
  end.

Definition count_frequency (numbers : list nat) : list (nat * nat) :=
  fold_left (fun acc n => inc_count n acc) numbers [].

Parameter complex_angle_3 : forall {A : Type}, A -> A -> R.

Definition total_data
    (CNOT_numses single_q_numses : list (list nat))
    (errors : list Q)
    (t lam : Q) : list (list nat) :=
  let baseN := map (fun e => Nat.add (Z.to_nat (Qnum ((2 * lam * lam * t * t) / e))) 1%nat) errors in
  let repeatedN := List.concat (List.repeat baseN 20) in
  map (fun cs =>
         let c := fst cs in
         let s := snd cs in
         map (fun p => Nat.add (fst p) (snd p))
             (combine (map (fun xn => Nat.add (fst xn) (snd xn)) (combine c repeatedN)) s))
      (combine CNOT_numses single_q_numses).

Parameter drop_min_elements : list R -> list R.
Definition model_function (x a b c : R) : R := a + exp (b * x + c).

(* File IO, plotting, numpy/torch, and subprocess orchestration remain abstract in Coq. *)
Parameter operation :
  list (list Q) -> string -> string -> Q -> nat -> list Q ->
  (list (list R) * list (list nat) * list (list nat) * list (list (nat * nat))).

Parameter spectra_operation : string -> string -> nat.

Parameter compilation_time_operation :
  list (list Q) -> string -> string -> Q -> nat -> list Q ->
  (list (list nat) * list (list nat) * list (list nat) * list R * list R).
