From Coq Require Import List.
From Coq Require Import List String ZArith QArith Reals.
Require Import QBlueUtility.
Require Import QBlueSyntax.
Require Import QBlueQdrift.

(*
Inductive Pauli : Type := PI | PX | PY | PZ.

Record PauliTerm : Type := {
  ops : nat -> Pauli;
  coeff : Q
}.
*)


(* use sum_w for lambda, use the same qdrift_step *)

(* only need to modify sample function. *)

Fixpoint trans_matrix_row' (h:lowprog) (n:nat) (size:nat) :=
  match h with [] => fun _ => 0
             | x::xs => fun i => if i =? (size - 1 - length xs) then (Rabs (fst (fst x)) / sum_w h n)%R else trans_matrix_row' xs n size i
  end.
Definition trans_matrix_row (h:lowprog) (n:nat) := trans_matrix_row' h n (length h).

(*the following might not right. *)
Fixpoint trans_matrix_init' (h:lowprog) (n:nat) (t:nat) :=
   match t with 0 => fun _ => fun _ => R0
              | S t' => fun i => if i =? t' then trans_matrix_row h n else trans_matrix_init' h n t' i
   end.
Definition trans_matrix_init h n := trans_matrix_init' h n (length h).

(*sample function is basically the same as QBlueQDrift, but now, we just need to sammple from nat -> R. *)
Parameter sample : (nat -> R) -> nat.

Definition mult_amp (h:lowprog_ten) (a:R) := (fst h * a, snd h).

Definition lambda (h:lowprog) n := sum_w h n.

Fixpoint marqsim_algo' (h:lowprog) (t:R) (n:nat) (tr:nat -> nat -> R) (ni:nat) (size:nat) (p:nat -> R) :=
  match ni with 0 => []
              | S na =>
          let j := sample p in 
          let e := nth_default (C0, fun _ => paulii) h j in
          let newp := tr j in
          (mult_amp (mult_amp e (lambda h n)) t)::(marqsim_algo' h t n tr na size newp)
  end.

(*need to implement how to construct tr. algorithm 2. *)
Definition marqsim_algo h t n tr ni := marqsim_algo' h t n tr ni (length h) (trans_matrix_row h n).

(* implement cost function for CNOT. *)
(*
Definition nth_default {A : Type} (d : A) (xs : list A) (i : nat) : A := nth i xs d.
*)
Definition CostMatrix := nat -> nat -> nat.
Definition matrix_lookup_nat (m : CostMatrix) (i j : nat) : nat := m i j.
 (* nth_default 0%nat (nth_default [] m i) j.  *)

Definition qabs (x : R) : R := if Rlt_le_dec x 0 then -x else x.

Definition pauli_eqb (a b : paulimat) : bool :=
  match a, b with
  | paulii, paulii | paulix, paulix | pauliy, pauliy | pauliz, pauliz => true
  | _, _ => false
  end.

Definition is_I (p : paulimat) : bool := pauli_eqb p paulii.
Definition is_XY (p : paulimat) : bool := orb (pauli_eqb p paulix) (pauli_eqb p pauliy).

Definition term_weight (t : lowprog_ten) : R := qabs (fst (fst t)).

Fixpoint lambda_sum (h : lowprog) : R :=
  match h with [] => 0%R
             | x::xs => term_weight x + lambda_sum xs
  end.


Definition normalize_probs (h : lowprog) : nat -> R :=
  let lam := lambda_sum h in
  if Rgt_dec lam 0
  then fun i => (Rdiv (term_weight (nth_default (C0, fun _ => paulii) h i)) lam)
  else fun _ => 0%R.


Fixpoint cnot_cost_ops (a b : nat -> paulimat) (n:nat) : nat :=
  match n with 0 => 0
            | S m => 
      let x := (a m) in let y := (b m) in
      let base := if pauli_eqb x y then 1%nat else 0%nat in
      let extra := if andb (negb (is_I x)) (negb (is_I y))
                   then if pauli_eqb x y then 1%nat else 0%nat
                   else 0%nat in
      base + extra + cnot_cost_ops a b m
  end.

Fixpoint xy_count (xs : nat -> paulimat) (n:nat) : nat :=
  match n with
  | 0 => 0%nat
  | S m => (if is_XY (xs m) then 1%nat else 0%nat) + xy_count xs m
  end.

Fixpoint xy_overlap (a b : nat -> paulimat) (n:nat) : nat :=
  match n with 0 => 0
            | S m => 
      let x := (a m) in let y := (b m) in
      (if andb (pauli_eqb x y) (is_XY x) then 1%nat else 0%nat) + xy_overlap a b m
  end.

Definition single_q_cost_ops (a b : nat -> paulimat) (n:nat) : nat :=
  xy_count a n + xy_count b n - 2 * xy_overlap a b n.

Fixpoint row_costs' (f : (nat -> paulimat) -> (nat -> paulimat) -> nat -> nat) (row : lowprog_ten) (all : lowprog) (n:nat) (size:nat) : nat -> nat :=
  match size with 0 => fun _ => Nat.zero
            | S m => fun i => if m =? i then f (snd row) (snd (nth_default (C0, fun _ => paulii) all i)) n else row_costs' f row all n m i
  end.
Definition row_costs f row all n := row_costs' f row all n (length all).

Definition get_CNOT_matrix (input_pauli : lowprog) (n:nat) : CostMatrix :=
  fun i => row_costs cnot_cost_ops (nth_default (C0, fun _ => paulii) input_pauli i) input_pauli n.

Definition get_single_q_matrix (input_pauli : lowprog) (n:nat) : CostMatrix :=
  fun i => row_costs single_q_cost_ops (nth_default (C0, fun _ => paulii) input_pauli i) input_pauli n.

(*implement algorithm 2, and then call marqsim_algo with tr being the output of algorithm 2. *)


(* below is the history code. 
Definition Hamiltonian := nat -> norm_ten.

Definition ProbMatrix := nat -> nat -> R.


Definition get_markov_0 (input_pauli : lowprog) (n:nat) : ProbMatrix :=
  let pro := normalize_probs input_pauli n in fun _ => pro.


Definition turn_norm_prog_ham (h:norm_prog) :=
 (fun i => if i <? length h then nth i h (0%R, (fun _ => paulii)) else (0%R, (fun _ => paulii)), length h).

(*
Definition nth_default {A : Type} (d : A) (xs : list A) (i : nat) : A := nth i xs d.
*)

Definition matrix_lookup_nat (m : CostMatrix) (i j : nat) : nat := m i j.
 (* nth_default 0%nat (nth_default [] m i) j.  *)

Definition qabs (x : R) : R := if Rlt_le_dec x 0 then -x else x.

Definition pauli_eqb (a b : paulimat) : bool :=
  match a, b with
  | paulii, paulii | paulix, paulix | pauliy, pauliy | pauliz, pauliz => true
  | _, _ => false
  end.

Definition is_I (p : paulimat) : bool := pauli_eqb p paulii.
Definition is_XY (p : paulimat) : bool := orb (pauli_eqb p paulix) (pauli_eqb p pauliy).

Definition term_weight (t : norm_ten) : R := qabs (fst t).

Fixpoint lambda_sum (h : Hamiltonian) (n:nat) : R :=
  match n with 0 => 0%R
             | S m => term_weight (h m) + lambda_sum h m
  end.


Definition normalize_probs (h : Hamiltonian) (n:nat) : nat -> R :=
  let lam := lambda_sum h n in
  if Rgt_dec lam 0
  then fun i => (Rdiv (term_weight (h i)) lam)
  else fun _ => 0%R.


Definition get_markov_0 (input_pauli : Hamiltonian) (n:nat) : ProbMatrix :=
  let pro := normalize_probs input_pauli n in fun _ => pro.

Fixpoint cnot_cost_ops (a b : nat -> paulimat) (n:nat) : nat :=
  match n with 0 => 0
            | S m => 
      let x := (a m) in let y := (b m) in
      let base := if pauli_eqb x y then 1%nat else 0%nat in
      let extra := if andb (negb (is_I x)) (negb (is_I y))
                   then if pauli_eqb x y then 1%nat else 0%nat
                   else 0%nat in
      base + extra + cnot_cost_ops a b m
  end.

Fixpoint xy_count (xs : nat -> paulimat) (n:nat) : nat :=
  match n with
  | 0 => 0%nat
  | S m => (if is_XY (xs m) then 1%nat else 0%nat) + xy_count xs m
  end.

Fixpoint xy_overlap (a b : nat -> paulimat) (n:nat) : nat :=
  match n with 0 => 0
            | S m => 
      let x := (a m) in let y := (b m) in
      (if andb (pauli_eqb x y) (is_XY x) then 1%nat else 0%nat) + xy_overlap a b m
  end.

Definition single_q_cost_ops (a b : nat -> paulimat) (n:nat) : nat :=
  xy_count a n + xy_count b n - 2 * xy_overlap a b n.

Fixpoint row_costs (f : (nat -> paulimat) -> (nat -> paulimat) -> nat -> nat) (row : norm_ten) (all : Hamiltonian) (n:nat) : nat -> nat :=
  match n with 0 => fun _ => 0
            | S m => fun i => if m =? i then f (snd row) (snd (all m)) n else row_costs f row all m i
  end.

Definition get_CNOT_matrix (input_pauli : Hamiltonian) (n:nat) : CostMatrix :=
  fun i => row_costs cnot_cost_ops (input_pauli i) input_pauli n.

Definition get_single_q_matrix (input_pauli : Hamiltonian) (n:nat) : CostMatrix :=
  fun i => row_costs single_q_cost_ops (input_pauli i) input_pauli n.

(* Bridge from Coq rationals/costs to integer capacities and stochastic perturbations. *)
Definition z_to_Q (z : Z) : Q := inject_Z z.

Definition z_round_half_up (num den : Z) : Z :=
  Z.div (num + Z.div den 2) den.

(* Matches Python: int(abs(coeff) * 10000 + 0.5). 
Definition scaled_capacity (q : Q) : Z :=
  let a := qabs q in
  let num := (Qnum a * 10000)%Z in
  let den := Z.pos (Qden a) in
  z_round_half_up num den.

Parameter perturb_weight : nat -> nat -> Z.
*)
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

*)