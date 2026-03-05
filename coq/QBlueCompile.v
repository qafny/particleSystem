(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueTrotter.
Require Import QBlue.QBlueQdrift.
Require Import QBlue.QBlueSynthDigital.
Require Import QBlue.QBlueSynth.
Require Import QBlue.QBlueTTS.
Require Import QBlue.QBlueMarQSim.


(* Translate from high-level hamiltonian to IBM digital gates
err: tolerance; t: time;
exp: high-level hamiltonian;
it: high-level hamiltonian type;
nbit: number of qubits for exp, length of it *)
Definition translate_highp2circ (err t : R) (exp : blueExp) (it : iota) (nbit : nat) 
  : ucom ExtractionGateSet.U :=
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in
  synth_digital_ibm t nbit lowp.

  
Definition translate (err t : R) (exp : blueExp) (it : iota) : lowprog := 
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in lowp.


Definition translate_lowp2circ_std (err t : R) (lp : lowprog) (nbit : nat) : ucom ExtractionGateSet.U := 
  let lowp : lowprog := trotter err t lp in 
  synth_digital_ibm t nbit lowp.

Definition translate_lowp2circ_std_2nd_order (err t : R) (lp : lowprog) (nbit : nat) : ucom ExtractionGateSet.U := 
  let lowp : lowprog := trotter_2nd_order err t lp in 
  synth_digital_ibm t nbit lowp.

Definition translate_lowp2circ_qdrift (err t : R) (lp : lowprog) (nbit : nat) 
: ucom ExtractionGateSet.U := 
  let lowp : lowprog := trotter_qdrift err t lp in 
  synth_digital_ibm t nbit lowp.

Definition translate_lowp2circ_marqsim (err t : R) (lp : lowprog) (nbit : nat) 
: ucom ExtractionGateSet.U := 
  let lowp : lowprog := trotter_marqsim err t lp nbit in 
  synth_digital_ibm t nbit lowp.


Definition translate_lowp2circ_TTS_LCU (err t : R) (lp : lowprog) (nbit : nat) 
: ucom ExtractionGateSet.U := 
  TTS_LCU err t nbit lp.

Definition translate_lowp2Indiana_std (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter err t lp in 
  synth_analog_indiana t nbit lowp.

Definition translate_lowp2Indiana_std_2nd_order (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter_2nd_order err t lp in 
  synth_analog_indiana t nbit lowp.

Definition translate_lowp2Indiana_qdrift (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter_qdrift err t lp in 
  synth_analog_indiana t nbit lowp.

Definition translate_lowp2Indiana_marqsim (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter_marqsim err t lp nbit in 
  synth_analog_indiana t nbit lowp.

Record Pipeline := {
  p_ham_sim : R -> R -> lowprog -> lowprog;
  p_synth   : R -> nat -> lowprog -> ucom ExtractionGateSet.U
}.

Definition get_cost (p : Pipeline) 
  (err t : R) (lp : lowprog) (nbit : nat) : nat  :=
  let lowp : lowprog := p.(p_ham_sim) err t lp in
  let c := p.(p_synth) t nbit lowp in 0%nat.


Definition ham_sim_list : list (R -> R -> lowprog -> lowprog) :=
  [trotter].

Definition synth_list : list (R -> nat -> lowprog -> ucom ExtractionGateSet.U) :=
  [synth_digital_ibm].


Fixpoint pipelines_for_hs
  (hs : R -> R -> lowprog -> lowprog)
  (sys : list (R -> nat -> lowprog -> ucom ExtractionGateSet.U))
  : list Pipeline :=
  match sys with
  | [] => []
  | sy :: sys' =>
      {| p_ham_sim := hs; p_synth := sy |} :: (pipelines_for_hs hs sys')
  end.


Fixpoint all_pipelines
  (hss : list (R -> R -> lowprog -> lowprog))
  (sys : list (R -> nat -> lowprog -> ucom ExtractionGateSet.U))
  : list Pipeline :=
  match hss with
  | [] => []
  | hs :: hss' =>
    (pipelines_for_hs hs sys) ++ all_pipelines hss' sys
  end.


Fixpoint greedy_best_pipeline
  (H : lowprog) (err t : R) (nbit : nat)
  (ps : list Pipeline)
  (best : Pipeline)
  : Pipeline :=
  match ps with
  | [] => best
  | p :: ps' =>
      let c_best := get_cost best err t H nbit in
      let c_p    := get_cost p err t H nbit in
      if c_p <? c_best 
      then greedy_best_pipeline H err t nbit ps' p 
      else greedy_best_pipeline H err t nbit ps' best 
  end.


Definition qblue_compile (H : lowprog) (err t : R) (nbit : nat)
(trotter_l : list (R -> R -> lowprog -> lowprog))
(synth_l : list (R -> nat -> lowprog -> ucom ExtractionGateSet.U)) 
: Pipeline :=
  let best := {|
    p_ham_sim := trotter;
    p_synth  := synth_digital_ibm;
    |} in
  greedy_best_pipeline H err t nbit (all_pipelines ham_sim_list synth_list) best.





