(* Based on TS expansion plus LCU *)
(* We use control gates to select Vj (with amplitude) uniformly wo considering the amplitude as weight, 
which is different from the original LCU. *)
From SQIR Require Import ExtractionGateSet.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueParTransJwt.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.

Definition get_nseg (t : R) (lp: lowprog) : nat := 
  let sum_coef := (fold_left (fun acc x => acc + Rabs((fst (fst x)))) lp 0)%R in
  ceilR_N (t * sum_coef / (ln 2)).

(* Use sum_{K+1}^inf x^k/k! = e^x x^{K+1}/(K+1)! *)
(* The K is the number of terms in the Taylor expansion. 
   The error is bounded by sum_{K+1}^inf x^k/k! = 2r (ln 2)^{K+1}/(K+1)! *) 

(* find the K such that (ln 2)^{K+1}/(K+1)! <= bound, iterate at most fuel times *)
Fixpoint findK_upto (fuel : nat) (bound aux : R) (k : nat) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
      if Rltb aux bound
      then k
      else findK_upto fuel' bound (aux * (ln 2) / (INR (S k))) (S k)
  end.

(* find K such that sum_{K+1}^inf x^k/k! <= err *)
Definition findK (err t : R) (lp : lowprog) := 
  let r := get_nseg t lp in
  let bound : R := (err / (2 * (INR r)))%R in
  findK_upto 20 bound (ln 2) 0.


(* (H1 + H2 + ...)^k *)
Fixpoint cal_lowp_power (nqubit k : nat) (lp : lowprog) : lowprog := 
  match k with
  | 0 => [(C1, fun x => paulii)]
  | S k' => plus_app_plus nqubit (cal_lowp_power nqubit k' lp) lp
end.

(* exp(-itH) = sum (-itH)^k/k! H^k *)
Fixpoint taylor_exp (t : R) (nqubit k : nat) (lp : lowprog) : lowprog := 
  match k with 
  | 0 => cal_lowp_power nqubit k lp
  | S k' => let ampli := Cmult (Cpow Ci k) (RtoC ((pow (- t) k) / (INR (factor k)))) in
    (mult_ampli_hplus ampli (cal_lowp_power nqubit k lp)) ++ (taylor_exp t nqubit k' lp)
  end.

(* map |nl><nl| to lowprog *)
Fixpoint cntl2pauli_helper (nl : list nat) : lowprog :=
  match nl with
  | x::ax => plus_ten_plus 1%nat (length ax) (unitstate2pauli x x) (cntl2pauli_helper ax)
  | [] => []
  end.

(* Build LCU: translate a unitary to SQIR base *)
Fixpoint LCU_digital_ibm (nqubit : nat) (vi : lowprog) : ucom ExtractionGateSet.U :=
  match vi with
  | [] => SKIP
  | (amp, f) :: app => useq (synth_digital_ibm_apauli (fst amp) nqubit f) (LCU_digital_ibm nqubit app)
  end.

(* Build each V with control bit: I+∣011⟩⟨011∣⊗(V−I):
idx: index of V; nqcn: # of control qubits; nqv: # of qubits in Vi; lp: list of Vi *)
Definition build_cntlV (lp : lowprog) (nqcn nqv idx: nat) : ucom ExtractionGateSet.U :=
  match nth_error lp idx with
  | None => SKIP
  | Some vi => 
    let nl := cnt2bin idx nqcn in
    let control := cntl2pauli_helper nl in
    let t2 := plus_ten_plus nqcn nqv control (vi :: (-C1, fun _ => paulii) :: nil) in
    LCU_digital_ibm (nqcn + nqv) ((C1, fun _ => paulii) :: t2)
  end.

(* Build circuit of one segment:
nqv: # of qubits of input program; input: lowprog after taylor expansion *)
Definition build_circuit_seg (nqv : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nterm := length input in
  let nqcn := Nat.log2_up nterm in
  let circ_list : list (ucom ExtractionGateSet.U) := map (build_cntlV input nqcn nqv) (seq 0 nterm) in
  let circ_cent := fold_left useq circ_list SKIP in
  let hadmard := fold_left (fun acc i => useq (H i) acc) (seq 0 nqcn) SKIP in
  useq (useq hadmard circ_cent) hadmard.

Definition TTS_LCU (err t: R) (nbit : nat) (input : lowprog) : ucom ExtractionGateSet.U :=
  let nseg := get_nseg t input in
  let k := findK err t input in
  let prog_seg := taylor_exp (t / (INR nseg)) nbit k input in
  let circ_seg := build_circuit_seg nbit prog_seg in
  fold_left (fun acc _ => useq circ_seg acc) (seq 0 nseg) SKIP.



