(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
From SQIR Require Import SQIR.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueTrotter.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Require Import QBlue.QBlueSynth.


(* Local Open Scope R_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope. *)



Definition translate (err t : R) (exp : blueExp) (it : iota) : list ugate := 
  let lowp1 : lowprog := bexp_to_lowprog exp it in
  let lowp : lowprog := trotter err t lowp1 in
  let nbit := length it in
  let fix helper (input_prog : lowprog) : list ugate :=
    match input_prog with 
    | [] => []
    | (_, _, x) :: ax => (synth_analog_indiana t nbit x) ++ (helper ax)
    end in
  helper lowp.

  
(*
(* This is for trotterization. Maybe need to modify later *)
(* exp(-i t H) *)
Parameter expH : R -> lowprog -> lowprog.


(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator_tt (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-myC1)%C [ten_app_ten h2 h1]).

Definition commutator_st (h1 : lowprog) (h2 : lowprog_ten) : lowprog :=
  let l1 := plus_app_ten h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (ten_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition commutator_ts (h1 : lowprog_ten) (h2 : lowprog) : lowprog :=
  let l1 := ten_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_ten h2 h1) in
  plus_plus_plus l1 l2.

(* Norm of H matrix *)
Parameter norm : lowprog -> R.


(* Drop first n elements of a list. *)
Fixpoint drop_nth {A : Set} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | S n', _ :: xs => drop_nth n' xs
  | _, [] => []
  end.

(* Eval compute in drop_nth 2 [10; 20; 30; 40]. 
Returns [30; 40] *)

Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with 
  | [] => []
  | h :: rem => commutator_st rem h
  end.

(* Outer sum: ∑_{γ1=1}^Γ || ∑_{γ2=γ1+1}^Γ [Hγ2, Hγ1] || *)
Fixpoint trotter_error_bound_helper (idx : nat) (hlist : lowprog) : R :=
  match idx with
  | 0 => 0
  | S k => let comm_sum := comm_sums idx hlist in
      Rplus (norm comm_sum) (trotter_error_bound_helper k hlist)
  end.

Definition trotter_error_bound (t : R) (hlist : lowprog) : R :=
  let gamma := length hlist in
  (t*t/2) * (trotter_error_bound_helper gamma hlist). 

(* Approx = exp(-itH_1)exp(-itH_2) ... *)
Fixpoint e_split (t : R) (hlist : lowprog) : lowprog :=
    match hlist with [] => []
    | h :: ht => plus_app_plus (expH t [h]) (e_split t ht)
    end.



(* Tight error bound for the second-order Suzuki formula. *)
Definition commutator_ss (h1 : lowprog) (h2 : lowprog) : lowprog :=
  let l1 := plus_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-myC1) (plus_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition suzuki_comm_sum_helper (hlist : lowprog) : (lowprog * lowprog) :=
  match hlist with 
  | [] => ([], [])
  | x :: rem => 
    let t1 := commutator_ss rem (commutator_st rem x) in
    let t2 := commutator_ts x (commutator_ts x rem) in (t1, t2)
    end.

Fixpoint suzuki_error_bound (t: R) (hlist : lowprog) : R :=
  match hlist with
  | [] => 0
  | x :: ax => let (term1, term2) := suzuki_comm_sum_helper hlist in
      Rplus (Rplus (Rdiv ((norm term1) * (pow t 3)) 12)
                   (Rdiv ((norm term2) * (pow t 3)) 24))
            (suzuki_error_bound t ax)
  end.

Definition e_split_suzuki (t : R) (hlist : lowprog) : lowprog := 
  let term1 : lowprog := e_split t (rev hlist) in
  let term2 : lowprog := e_split t hlist in
  plus_app_plus term1 term2.
*)


(*
(* synthesization *)
(* 1. to basic gates of CNOT, H, Rz, Collect parity on the last qubit *)
(* Map X and Y to Z, X = HZH, Y=Rz(pi/2) HZH Rz(-pi/2) *)
(* nbit: # of bits in circuit; curbit: id of the pauli in the string; s: the current pauli to convert 
return: the converting matrix: for Y, return Rz; H and H; Rz) *)
Definition map_pauli2gate_zbase_lr (nbit curbit: nat) (s : paulimat)
: ((base_ucom nbit) * (base_ucom nbit)) :=
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


