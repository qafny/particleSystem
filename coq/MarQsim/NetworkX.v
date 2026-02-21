From Coq Require Import List ZArith Bool.
Import ListNotations.
Open Scope Z_scope.

(* Coq translation of the subset of NetworkX used by MarQSim. *)
Inductive Node : Type :=
| NSrc
| NSink
| NB (idx : nat)
| NC (idx : nat).

Definition node_eqb (a b : Node) : bool :=
  match a, b with
  | NSrc, NSrc => true
  | NSink, NSink => true
  | NB i, NB j => Nat.eqb i j
  | NC i, NC j => Nat.eqb i j
  | _, _ => false
  end.

Record EdgeAttr : Type := {
  capacity : Z;
  weight : Z
}.

Record Edge : Type := {
  src : Node;
  dst : Node;
  attr : EdgeAttr
}.

Definition edge_eqb (e1 e2 : Edge) : bool :=
  andb (node_eqb (src e1) (src e2))
       (andb (node_eqb (dst e1) (dst e2))
             (andb (Z.eqb (capacity (attr e1)) (capacity (attr e2)))
                   (Z.eqb (weight (attr e1)) (weight (attr e2))))).

Record DiGraph : Type := {
  demands : list (Node * Z);
  edges : list Edge
}.

Definition empty_graph : DiGraph := {| demands := []; edges := [] |}.

Definition set_node_demand (g : DiGraph) (n : Node) (d : Z) : DiGraph :=
  let fix upsert (xs : list (Node * Z)) : list (Node * Z) :=
      match xs with
      | [] => [(n, d)]
      | (k, v) :: tl =>
          if node_eqb k n then (n, d) :: tl else (k, v) :: upsert tl
      end
  in
  {| demands := upsert (demands g); edges := edges g |}.

Definition add_edge (g : DiGraph) (e : Edge) : DiGraph :=
  {| demands := demands g; edges := e :: edges g |}.

Definition add_edges_from (g : DiGraph) (es : list Edge) : DiGraph :=
  fold_left add_edge es g.

Definition outgoing (g : DiGraph) (n : Node) : list Edge :=
  filter (fun e => node_eqb (src e) n) (edges g).

Definition incoming (g : DiGraph) (n : Node) : list Edge :=
  filter (fun e => node_eqb (dst e) n) (edges g).

Definition FlowDict := list ((Node * Node) * Z).

Definition flow_lookup (f : FlowDict) (u v : Node) : Z :=
  fold_left
    (fun acc kv =>
       let '(uv, x) := kv in
       let '(uu, vv) := uv in
       if andb (node_eqb uu u) (node_eqb vv v) then x else acc)
    f 0.

Definition edge_flow (f : FlowDict) (e : Edge) : Z :=
  flow_lookup f (src e) (dst e).

Definition flow_cost (g : DiGraph) (f : FlowDict) : Z :=
  fold_left (fun acc e => acc + edge_flow f e * weight (attr e)) (edges g) 0.

Definition edge_capacity_ok (f : FlowDict) (e : Edge) : Prop :=
  0 <= edge_flow f e <= capacity (attr e).

Definition node_balance (g : DiGraph) (f : FlowDict) (n : Node) : Z :=
  let in_sum := fold_left (fun acc e => acc + edge_flow f e) (incoming g n) 0 in
  let out_sum := fold_left (fun acc e => acc + edge_flow f e) (outgoing g n) 0 in
  in_sum - out_sum.

Definition demand_of (g : DiGraph) (n : Node) : Z :=
  fold_left
    (fun acc nd =>
       let '(k, d) := nd in
       if node_eqb k n then d else acc)
    (demands g) 0.

Definition flow_feasible (g : DiGraph) (f : FlowDict) : Prop :=
  (forall e, In e (edges g) -> edge_capacity_ok f e) /\
  (forall nd,
      In nd (demands g) ->
      let '(n, _) := nd in
      node_balance g f n = demand_of g n).

(*

(* Define the basic types for the network *)
Definition Node := nat.
Definition Capacity := Z.
Definition Cost := Z.
Definition Flow := Z.

Record Edge := { u: Node; v: Node; cap: Capacity; cost: Cost }.
Definition Network := list Edge.

(* Successive Shortest Path main loop logic *)
Fixpoint ssp_iteration (fuel: nat) (net: Network) (imbalance: list Z) : Network :=
  match fuel with

  | 0 => net (* Out of fuel, return current flow *)
  | S f' =>
      let s := find_source imbalance in (* Node with e(v) > 0 *)
      let t := find_sink imbalance in   (* Node with e(v) < 0 *)
      match find_shortest_path net s t with

      | Some path => 
          let delta := calculate_augmentation path imbalance in
          let new_net := augment_flow net path delta in
          let new_imbalance := update_imbalance imbalance path delta in
          ssp_iteration f' new_net new_imbalance
      | None => net (* No path found, algorithm terminates *)
      end
  end.

*)

(* Spec-level translation of networkx.network_simplex. *)
Parameter network_simplex : DiGraph -> Z * FlowDict.

Axiom network_simplex_feasible :
  forall g,
    let '(_, f) := network_simplex g in
    flow_feasible g f.

Axiom network_simplex_optimal :
  forall g f',
    flow_feasible g f' ->
    let '(cost, f) := network_simplex g in
    cost = flow_cost g f /\ cost <= flow_cost g f'.
