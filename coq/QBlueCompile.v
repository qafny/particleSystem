(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
From SQIR Require Import ExtractionGateSet.
From VOQC Require Import FullGateSet.
From VOQC Require Import Main.

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
Require Import QBlue.QBlueQuantumWalk.


Module EG := ExtractionGateSet.
(* number of samples used to estimate the # of gates per sample: 100 *)
Parameter nsampe_gatesize_est : nat.
(* # of gates in one chunk: 20000 *)
Parameter ngates_per_chunk : nat. 

(* Translate from high-level hamiltonian to IBM digital gates
err: tolerance; t: time;
exp: high-level hamiltonian;
it: high-level hamiltonian type;
nbit: number of qubits for exp, length of it *)
Definition translate_highp2circ (err t : R) (exp : blueExp) (it : iota) (nbit : nat) : EG.ucom EG.U :=
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in
  synth_digital_ibm t nbit lowp.


Definition translate_lowp2circ_std (err t : R) (lp : lowprog) (nbit : nat) : EG.ucom EG.U := 
  let lowp : lowprog := trotter err t lp in 
  synth_digital_ibm t nbit lowp.

Definition translate_lowp2circ_std_2nd_order (err t : R) (lp : lowprog) (nbit : nat) : EG.ucom EG.U := 
  let lowp : lowprog := trotter_2nd_order err t lp in 
  synth_digital_ibm t nbit lowp.

Definition ngates_per_term (t : R) (lp : lowprog) (nbit : nat) (totw : R) : nat :=
  let lowp_sample := sample lp nsampe_gatesize_est totw in
  let circ := synth_digital_ibm t nbit lowp_sample in
  Nat.div (ucom_gate_count circ) nsampe_gatesize_est.


Fixpoint translate_lowp2circ_chunks_acc (t : R) (lp : lowprog) (ist nbit : nat) (scale : R)
  (* (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) *)
  (f_translate : lowprog -> nat -> nat -> R -> R -> nat -> EG.ucom EG.U)
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit)
  (fuel remaining_samples ns : nat) (acc_rev : full_ucom_l nbit)
  : full_ucom_l nbit :=
  match fuel with
  | O => acc_rev
  | S fuel' =>
    match remaining_samples with
    | O => acc_rev
    | S _ =>
      let this_chunk := Nat.min ns remaining_samples in
      let cc := f_translate lp ist nbit scale t this_chunk in
      let opt := f_opt cc in
      translate_lowp2circ_chunks_acc t lp (ist + this_chunk) nbit scale f_translate f_opt fuel'
        (remaining_samples - this_chunk) ns
        (List.rev_append opt acc_rev)
    end
  end.

Definition translate_lowp2circ_chunks (t : R) (lp : lowprog) (ist nbit : nat) (scale : R)
  (* (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) *)
  (f_translate : lowprog -> nat -> nat -> R -> R -> nat -> EG.ucom EG.U)
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit)
  (fuel remaining_samples ns : nat) (acc_rev : full_ucom_l nbit)
  : full_ucom_l nbit :=
  List.rev
    (translate_lowp2circ_chunks_acc t lp ist nbit scale f_translate f_opt
       fuel remaining_samples ns acc_rev).
  
Definition translate_stdTrotter_ibmdigi (lp : lowprog) (ist nbit : nat) 
  (scale t : R) (sp_size : nat) : EG.ucom EG.U := 
  let lowp := firstn sp_size (skipn ist lp) in
  let lp1 := mult_r_hplus scale lowp in
  synth_digital_ibm t nbit lp1.

Definition translate_lowp2circ_stdTrotter (err t : R) (lp : lowprog) (nbit : nat)
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit) : full_ucom_l nbit :=
  let r := trotter_step err t lp in
  let nt := length lp in
  let totw := sum_w lp nt in
  let scale := (R1 / INR r) % R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div nt ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2circ_chunks t lp 0%nat nbit scale 
  translate_stdTrotter_ibmdigi f_opt nch nt ns []
  end.

Definition translate_lowp2circ_2ndTrotter (err t : R) (lp : lowprog) (nbit : nat) 
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit) : full_ucom_l nbit :=
  let r := trotter_step_2nd_order err t lp in
  let nt := length lp in
  let totw := sum_w lp nt in
  let scale := (R1 / R2 / INR r) % R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div nt ns)%nat) in
  match ns with
  | O => []
  | S _ => 
    let acc1 := translate_lowp2circ_chunks_acc t (rev lp) 0%nat nbit scale
      translate_stdTrotter_ibmdigi f_opt nch nt ns [] in
    List.rev
      (translate_lowp2circ_chunks_acc t lp 0%nat nbit scale
         translate_stdTrotter_ibmdigi f_opt nch nt ns acc1)
  end.


Definition translate_qdrift_ibmdigi (totw : R) (lp : lowprog) (ist nbit : nat)
  (scale t : R) (sp_size : nat) : EG.ucom EG.U := 
  let lp1 := sample lp sp_size totw in
  let lowp := mult_r_hplus scale lp1 in
  synth_digital_ibm t nbit lowp.


Definition translate_lowp2circ_qdrift (err t : R) (lp : lowprog) (nbit : nat) 
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit) : full_ucom_l nbit :=
  let N := qdrift_step err t lp in
  let totw := sum_w lp (length lp) in
  let scale := (totw / INR N)%R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div N ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2circ_chunks t lp 0%nat nbit scale 
  (translate_qdrift_ibmdigi totw) f_opt nch N ns []
  end.


Definition translate_marqsim_ibmdigi (prob_init : list R) (trans_matrix : nat -> list R)
  (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) : EG.ucom EG.U :=
  let lp1 := gen_lowprog_markov lp sp_size prob_init trans_matrix in
  let lowp := mult_r_hplus scale lp1 in
  synth_digital_ibm t nbit lowp.

Definition translate_lowp2circ_marqsim (err t : R) (lp : lowprog) (nbit : nat) 
  (f_opt : EG.ucom EG.U -> full_ucom_l nbit) 
  (f_mat : nat -> list R) : full_ucom_l nbit :=
  let N := qdrift_step err t lp in
  let prob_init := get_coef lp in
  let totw := sum_w lp (length lp) in
  let scale := (totw / INR N)%R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div N ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2circ_chunks t lp 0%nat nbit scale
    (translate_marqsim_ibmdigi prob_init f_mat) f_opt nch N ns []
  end.

Definition translate_lowp2circ_TTS_LCU (err t : R) (lp : lowprog) (nbit : nat) : EG.ucom EG.U := 
  TTS_LCU err t nbit lp.


Definition translate_lowp2circ_qwalk (err t : R) (lp : lowprog) (nbit : nat) : EG.ucom EG.U :=
  let nterm        := length lp in
  let n_inner_anc  := Nat.log2_up nterm in
  (* Compute |alpha_j| and lambda = sum |alpha_j| *)
  let coeffs       := map (fun term => Rabs (fst (fst term))) lp in
  let lam          := fold_left Rplus coeffs R0 in
  let tau          := (lam * t)%R in
  (* Gap 3 fix: Bessel-tail truncation *)
  let K            := QBlueQuantumWalk.findK_qwalk tau err in
  let n_outer_anc  := Nat.log2_up (S K) in
  let aux          := n_inner_anc + nbit in
  let outer_base   := aux + 1 in
  (* Gap 2 fix: coefficient-weighted inner PREP *)
  let inner_PREP   := QBlueQuantumWalk.build_inner_prep coeffs lam n_inner_anc in
  (* SELECT oracle *)
  let circ_list    := map (build_cntlV lp n_inner_anc nbit) (seq 0 nterm) in
  let SELECT       := fold_left EG.useq circ_list EG.SKIP in
  (* Gap 1 fix: Bessel-weighted outer PREPARE *)
  let outer_PREP   := QBlueQuantumWalk.build_outer_prep tau K outer_base n_outer_anc in
  QBlueQuantumWalk.build_qwalk_lcu_circuit
    inner_PREP SELECT outer_PREP tau n_inner_anc aux K outer_base n_outer_anc.


(* Translate to Indiana Analog by chunks *)
Fixpoint translate_lowp2IndiAna_chunks_acc (t : R) (lp : lowprog) (ist nbit : nat) (scale : R)
  (* (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) *)
  (f_translate : lowprog -> nat -> nat -> R -> R -> nat -> list ugate)
  (fuel remaining_samples ns : nat) (acc_rev : list ugate)
  : list ugate :=
  match fuel with
  | O => acc_rev
  | S fuel' =>
    match remaining_samples with
    | O => acc_rev
    | S _ =>
      let this_chunk := Nat.min ns remaining_samples in
      let cc := f_translate lp ist nbit scale t this_chunk in
      translate_lowp2IndiAna_chunks_acc t lp (ist + this_chunk) nbit scale f_translate fuel'
        (remaining_samples - this_chunk) ns
        (List.rev_append cc acc_rev)
    end
  end.

Definition translate_lowp2IndiAna_chunks (t : R) (lp : lowprog) (ist nbit : nat) (scale : R)
  (* (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) *)
  (f_translate : lowprog -> nat -> nat -> R -> R -> nat -> list ugate)
  (fuel remaining_samples ns : nat) (acc_rev : list ugate) : list ugate :=
  List.rev
    (translate_lowp2IndiAna_chunks_acc t lp ist nbit scale f_translate 
       fuel remaining_samples ns acc_rev).

Definition translate_stdTrotter_indiAna (lp : lowprog) (ist nbit : nat) 
  (scale t : R) (sp_size : nat) : list ugate := 
  let lowp := firstn sp_size (skipn ist lp) in
  let lp1 := mult_r_hplus scale lowp in
  synth_analog_indiana t nbit lp1.


Definition translate_lowp2IndiAna_stdTrotter (err t : R) (lp : lowprog) (nbit : nat) : list ugate :=
  let r := trotter_step err t lp in
  let nt := length lp in
  let totw := sum_w lp nt in
  let scale := (R1 / INR r) % R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div nt ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2IndiAna_chunks t lp 0%nat nbit scale 
  translate_stdTrotter_indiAna nch nt ns []
  end.

Definition translate_lowp2IndiAna_2ndTrotter (err t : R) (lp : lowprog) (nbit : nat) : list ugate :=
  let r := trotter_step_2nd_order err t lp in
  let nt := length lp in
  let totw := sum_w lp nt in
  let scale := (R1 / R2 / INR r) % R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div nt ns)%nat) in
  match ns with
  | O => []
  | S _ => 
    let acc1 := translate_lowp2IndiAna_chunks_acc t (rev lp) 0%nat nbit scale
      translate_stdTrotter_indiAna nch nt ns [] in
    List.rev
      (translate_lowp2IndiAna_chunks_acc t lp 0%nat nbit scale
         translate_stdTrotter_indiAna nch nt ns acc1)
  end.


Definition translate_qdrift_indiAna (totw : R) (lp : lowprog) (ist nbit : nat)
  (scale t : R) (sp_size : nat) : list ugate := 
  let lp1 := sample lp sp_size totw in
  let lowp := mult_r_hplus scale lp1 in
  synth_analog_indiana t nbit lowp.

Definition translate_lowp2IndiAna_qdrift (err t : R) (lp : lowprog) (nbit : nat) : list ugate :=
  let N := qdrift_step err t lp in
  let totw := sum_w lp (length lp) in
  let scale := (totw / INR N)%R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div N ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2IndiAna_chunks t lp 0%nat nbit scale 
  (translate_qdrift_indiAna totw) nch N ns []
  end.


Definition translate_marqsim_indiAna (prob_init : list R) (trans_matrix : nat -> list R)
  (lp : lowprog) (ist nbit : nat) (scale t : R) (sp_size : nat) : list ugate :=
  let lp1 := gen_lowprog_markov lp sp_size prob_init trans_matrix in
  let lowp := mult_r_hplus scale lp1 in
  synth_analog_indiana t nbit lowp.

Definition translate_lowp2IndiAna_marqsim (err t : R) (lp : lowprog) (nbit : nat) 
(f_mat : nat -> list R) : list ugate :=
  let N := qdrift_step err t lp in
  let prob_init := get_coef lp in
  let totw := sum_w lp (length lp) in
  let scale := (totw / INR N)%R in
  let ns := Nat.div ngates_per_chunk (ngates_per_term t lp nbit totw) in
  let nch := S ((Nat.div N ns)%nat) in
  match ns with
  | O => []
  | S _ => translate_lowp2IndiAna_chunks t lp 0%nat nbit scale
    (translate_marqsim_indiAna prob_init f_mat) nch N ns []
  end.

(* Translate to IBM Analog *)
Definition translate_lowp2IBMAna_stdTrotter (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter err t lp in 
  synth_analog_ibm t nbit lowp.

Definition translate_lowp2IBMAna_std_2ndTrotter (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter_2nd_order err t lp in 
  synth_analog_ibm t nbit lowp.

Definition translate_lowp2IBMAna_qdrift (err t : R) (lp : lowprog) (nbit : nat) : list ugate := 
  let lowp : lowprog := trotter_qdrift err t lp in 
  synth_analog_ibm t nbit lowp.

Definition translate_lowp2IBMAna_marqsim (err t : R) (lp : lowprog) (nbit : nat) 
(f_mat : nat -> list R) : list ugate :=  
let lowp : lowprog := trotter_marqsim err t lp nbit f_mat in 
  synth_analog_ibm t nbit lowp.



(* The following optimization would be in ocaml
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
*)
