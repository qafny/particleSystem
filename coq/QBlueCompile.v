(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueTrotter.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueSynthDigital.


(* Translate from high-level hamiltonian to IBM digital gates
err: tolerance; t: time;
exp: high-level hamiltonian;
it: high-level hamiltonian type;
nbit: number of qubits for exp, length of it *)
Definition translate1 (err t : R) (exp : blueExp) (it : iota) (nbit : nat) 
  : ucom ExtractionGateSet.U :=
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in
  synth_digital_ibm t nbit lowp.

  
Definition translate (err t : R) (exp : blueExp) (it : iota) : lowprog := 
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in lowp.



(*
(* synthesization *)
(* 1. to basic gates of CNOT, H, Rz, Collect parity on the last qubit *)
(* Map X and Y to Z, X = HZH, Y=Rz(pi/2) HZH Rz(-pi/2) *)
(* nbit: # of bits in circuit; curbit: id of the pauli in the string; s: the current pauli to convert 
return: the converting matrix: for Y, return Rz; H and H; Rz) *)
Definition map_pauli2gate_zbase_lr (nbit curbit: nat) (s : paulimat)
:uuu ((base_ucom nbit) * (base_ucom nbit)) :=
  match s with 
  | pauliy => (useq (P curbit) (H curbit), useq (H curbit) (PDAG curbit))
  | paulix => (H curbit, H curbit) 
  | _ => (ID curbit,  ID curbit)
  end.

(* Return the CNOT connecting the current bit and target bit, the middle part of the circuit *)
Definition map_pauli2gate_zbase_m (nbit curbit tarbit : nat) (s : paulimat) : base_ucom nbit :=
  if curbit =? tarbit then ID curbit else
  match s with 
  | paulii => ID curbit
  | _ => CNOT curbit tarbit
  end.

(* Helper function for converting digital circuits using H, S and CNOT *)
(* nqubit: # of bits in circuit; qid: current bit; pauli_str: pauli string
left mid right: auxilla for saving the converted circuit *)
Fixpoint synth_digital_helper (nqubit qid : nat) (pauli_str : nat -> paulimat)
  (left mid right : base_ucom nqubit)
  : (base_ucom nqubit) * (base_ucom nqubit) * (base_ucom nqubit) :=
  match qid with
  | 0 => ((left, mid), right)
  | S qid' =>
      let (cur1, cur3) := map_pauli2gate_zbase_lr nqubit qid' (pauli_str qid') in
      let cur2 := map_pauli2gate_zbase_m nqubit qid' 0 (pauli_str qid') in
      synth_digital_helper nqubit qid' pauli_str (useq left cur1) (useq mid cur2) (useq right cur3)
  end.

(* Synthesization
nqubit: # of bits in circuit; pauli_str: pauli string;
return: sequence of unitary gate of the converted circuit *)
Definition synth_digital (nqubit : nat) (pauli_str : nat -> paulimat) : base_ucom nqubit :=
  let (left_mid, right) := synth_digital_helper nqubit nqubit pauli_str SKIP SKIP SKIP in
  let (left, mid) := left_mid in
  useq left (useq mid right).


(* 2. to gates of IBM analog, X, Z, ZZ gates *)
(* fill_pl 3 2 X => I tensor I tensor X *)
Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if eqb x a then true else inb eqb a xs
  end.

Definition fill_pl (nbit : nat) (reg : list nat) (p : paulimat) : lowprog_ten :=
  let f := (fun id => if (inb Nat.eqb id reg) then p else paulii) in (myC1, nbit, f).

Local Close Scope nat_scope.

(* H = exp(-i pi/4 X) exp(-i pi/4 Z) exp(-i pi/4 X). For IBM *)
(* H unitary gate on X and Z basis.
   nbit: # of bits in circuit; qid: id of the current bit *)
Definition H_u (nbit qid : nat) : list ugate := 
  let xu := exp_ugate (PI/R4) [fill_pl nbit [qid] paulix] in
  let zu := exp_ugate (PI/R4) [fill_pl nbit [qid] pauliz] in
  xu :: zu :: xu :: nil. 

(* S = exp(-i pi/4 Z) *)
Definition S_u (nbit qid : nat) : list ugate := 
  let zu := exp_ugate (PI/R4) [fill_pl nbit [qid] pauliz] in zu :: nil.

(* S^+ = exp(-i 7 pi/4 Z) *)
Definition SDag_u (nbit qid : nat) : list ugate := 
  let zu := exp_ugate (R7 * PI/R4) [fill_pl nbit [qid] pauliz] in zu :: nil. 

(* Find the nonI in pauli_str. qid starts from the length of pauli_str. *)
Fixpoint find_nonI (qid : nat) (pauli_str : nat -> paulimat) : list nat :=
  match qid with 
  | 0 %nat => []
  | S n => let aux := find_nonI n pauli_str in
    (if (paulimat_eqb (pauli_str n) paulii) then aux else n :: aux)
  end.  

(* Input is 2-local. Convert to X, Z, ZZ basis *)
Fixpoint synth_analog_ibm_helper (ml : list nat) (nbit : nat) (pauli_str : nat -> paulimat) : 
  (list ugate) * (list ugate) :=
  match ml with 
  | [] => ([], [])
  | m :: ax => let (left, right) := synth_analog_ibm_helper ax nbit pauli_str in
    let hu := H_u nbit m in
    let su := S_u nbit m in 
    let sdagu := SDag_u nbit m in
    let (app1, app2) := 
      match (pauli_str m) with 
      | paulix => (hu, hu)
      | pauliy => (su ++ hu, hu ++ sdagu)
      | _ => ([], []) 
      end in
    (left ++ app1, app2 ++ right) end.

Definition synth_analog_ibm (t : R) (nbit : nat) (pauli_str : nat -> paulimat) 
  : list ugate :=
  let ml := find_nonI nbit pauli_str in 
  if Nat.leb (length ml) 2 then
    let mid := exp_ugate t [fill_pl nbit ml pauliz] in
    let (left, right) := synth_analog_ibm_helper ml nbit pauli_str in
    left ++ [mid] ++ right
  else [].


(* 3. Input is any-local. Convert to Z, X...X basis *)
Fixpoint synth_analog_indiana_helper (ml : list nat) (nbit : nat) (pauli_str : nat -> paulimat) : 
  (list ugate) * (list ugate) :=
  match ml with 
  | [] => ([], [])
  | m :: ax => let (left, right) := synth_analog_indiana_helper ax nbit pauli_str in
    let hu := H_u nbit m in
    let su := S_u nbit m in 
    let sdagu := SDag_u nbit m in
    let (app1, app2) := 
      match (pauli_str m) with 
      | pauliy => (su, sdagu)
      | pauliz => (hu, hu)
      | _ => ([], []) 
      end in
    (left ++ app1, app2 ++ right) end.

Definition synth_analog_indiana (t : R) (nbit : nat) (pauli_str : nat -> paulimat) 
  : list ugate :=
  let ml := find_nonI nbit pauli_str in 
  let mid := exp_ugate t [fill_pl nbit ml paulix] in
  let (left, right) := synth_analog_indiana_helper ml nbit pauli_str in
  left ++ [mid] ++ right.
*)


Require Import List.
Require Import Nat.
Import ListNotations.

(* Existing types *)
Parameter Hamiltonian : Type.
Parameter IR : Type.

(* Existing cost type and projections *)
Parameter Cost : Type.
Parameter gate_count : Cost -> nat.
Parameter sim_time   : Cost -> nat.

Record HamSim := {
  ham_sim_apply : Hamiltonian -> IR;
  ham_sim_cost  : Hamiltonian -> Cost
}.

Record Synth := {
  synth_apply : IR -> IR;
  synth_cost  : IR -> Cost
}.

(*
Parameter trotter       : HamSim.
Parameter qdrift        : HamSim.
Parameter marqsim       : HamSim.
Parameter taylor        : HamSim.
Parameter quantum_walk  : HamSim.

Parameter synth_digital_ibm : Synth.
(* others can be added later *)

Definition ham_sim_list1 : list HamSim :=
  [trotter; qdrift; marqsim; taylor; quantum_walk].

Definition synth_list1 : list Synth :=
  [synth_digital_ibm].

Record Pipeline1 := {
  p_ham_sim1 : HamSim;
  p_synth1   : Synth
}. *)

Parameter cost_add : Cost -> Cost -> Cost.

(* Definition pipeline_cost (H : Hamiltonian) (p : Pipeline1) (err t : R) : Cost :=
  let c1 := p.(p_ham_sim1).(ham_sim_cost) H in
  let ir := p.(p_ham_sim1).(ham_sim_apply) H in
  let c2 := p.(p_synth1).(synth_cost) ir in
  cost_add c1 c2. *)

Record Pipeline := {
  p_ham_sim : R -> R -> lowprog -> lowprog;
  p_synth   : nat -> lowprog -> ucom ExtractionGateSet.U
}.

Definition get_cost (p : Pipeline) 
  (err t : R) (lp : lowprog) (nbit : nat) : nat  :=
  let lowp : lowprog := p.(p_ham_sim) err t lp in
  let c := p.(p_synth) nbit lowp in 0%nat.


Definition cost_better (c1 c2 : Cost) : bool :=
  Nat.ltb (gate_count c1) (gate_count c2)
  || (Nat.eqb (gate_count c1) (gate_count c2)
      && Nat.ltb (sim_time c1) (sim_time c2)).


Definition ham_sim_list : list (R -> R -> lowprog -> lowprog) :=
  [trotter].

Definition synth_list : list (R -> nat -> lowprog -> ucom ExtractionGateSet.U) :=
  [synth_digital_ibm].

Definition all_pipelines : list Pipeline :=
  flat_map
    (fun hs =>
       map (fun sy =>
              {| p_ham_sim := hs;
                 p_synth   := sy |})
           synth_list)
    ham_sim_list. 


Fixpoint greedy_best_pipeline
  (H : lowprog) (err t : R)
  (ps : list Pipeline)
  (best : Pipeline)
  (nbit : nat)
  : Pipeline :=
  match ps with
  | [] => best
  | p :: ps' =>
      let c_best := get_cost best err t H nbit in
      let c_p    := get_cost p err t H nbit in
      if c_p <? c_best 
      then greedy_best_pipeline H err t ps' p nbit
      else greedy_best_pipeline H err t ps' best nbit
  end.



Definition qblue_compile (H : lowprog) (err t : R)
(trotter_l : list HamSim) (synth_l : list Synth)
: Pipeline :=
  greedy_best_pipeline H err t () [].




