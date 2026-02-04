Require Import Reals.
Require Import QuantumLib.Complex.

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.

Local Open Scope nat_scope.

(* perturbative gadgtization *)
(* Define H^gad. *)
(* 1/2(I - Z_i Z_j) *)
(* i: any qubit before j; j: the last qubit; k: length of one term *)
Definition Hanc_sndq_helper (i j: nat) : lowprog :=
  let term1 := (RtoC(R1/R2), fun _ => paulii) in
  let f := fun idx => (if (Nat.eqb idx i || Nat.eqb idx j) then pauliz else paulii) in
  let term2 := (RtoC(-R1/R2), f) in 
  term1 :: term2 :: nil.

(* sum_{1<=i<j}} 1/2(I - Z_i Z_j), sum over i from 1 to j-1 *)
(* j: the last qubit; k: length of one term *)
Fixpoint Hanc_sndq (i j: nat) : lowprog :=
  match i with
  | 0 => []
  | S n => let term := Hanc_sndq_helper i j in
  plus_plus_plus term (Hanc_sndq n j)
  end.


(* sum over j from 2 to k *)
Fixpoint Hanc_fstq (j : nat) : lowprog :=
  match j with
  | 0 => []
  | 1 => []
  | S n' => let term := Hanc_sndq n' j in
  plus_plus_plus term (Hanc_fstq n') end.

(* H_s^{anc}, add I to make its length n+kr.
nc: number of computational qubits;
nht: r, number of tensor terms; 
htid: 0 to r-1, ternsor term id; 
k: size of the largest term.
*)
Fixpoint Hanc_aterm_helper (n1 n2 nori: nat) (pre post : lowprog_ten) (hori : lowprog) : lowprog :=
  match hori with
  | [] => []
  | x :: ax => (ten_ten_ten n1 (nori+n2) pre (ten_ten_ten nori n2 x post)) :: 
    (Hanc_aterm_helper n1 n2 nori pre post ax)
  end.

(* H_s^{anc} = sum_{1<=i<j} sum_{i<j<=k} [1/2 (I - Z_{s,i} Z_{s,j})] *)
Definition Hanc_aterm (nc nht htid k : nat) : lowprog := 
  let hori : lowprog := Hanc_fstq k in
  let pre : lowprog_ten := (C1, fun _ => paulii) in 
  let post := (C1, fun _ => paulii) in 
  Hanc_aterm_helper (nc + htid * k) ((nht-htid-1) * k) k pre post hori.


(* c_{s,j} sigma_{s,j} X_{s, j} *)
(* nht: r, number of tensor terms; 
  htid: 0 to r-1, ternsor term id; 
  ncid: 0 to nq-1, qubit id in the tensor H^{comp} including I 
  k: size of the largest term;
  kid: the kid_th computation qubit in one tensor term (excluding I).
  nq: nqubit of lowprog_ten ht
*)
Definition HV_qcomp (nht htid ncid k kid nq: nat) (ht : lowprog_ten) : lowprog_ten := 
  let (amp, f) := ht in  
  let id_anc := (nq + htid * k + kid) in
  let cs : C := if kid =? 1 then amp else C1 in
  let g := fun idx => 
    (if (idx =? ncid) && (Nat.leb ncid nq) then f idx 
      else if idx =? id_anc then paulix 
      else paulii) in (cs, g).

(* find the id of the computational qubit starting from curid *)
Fixpoint locate_ncid_aux (fuel nq curid : nat) (f : nat -> paulimat) : nat :=
  match fuel with
  | 0 => nq  (* give up *)
  | S fuel' =>
      if curid =? nq then nq
      else if paulimat_eqb (f curid) paulii
           then locate_ncid_aux fuel' nq (curid + 1) f
           else curid
  end.

Definition locate_ncid (nq curid : nat) (f : nat -> paulimat) : nat :=
  locate_ncid_aux (nq - curid) nq curid f.

(* V = sum_1^k c_{s,j} sigma_{s, j} X_{s, j} *)
Definition HV_aterm (nht htid k nq : nat) (ht : lowprog_ten) : lowprog := 
  let (amp, f) := ht in  
  let fix helper (curid kid : nat) : lowprog :=
    match kid with
    | 0 => [] (* all k terms already expanded *)
    | S k' => 
      let ncid := locate_ncid nq curid f in   
      (HV_qcomp nht htid ncid k kid nq ht) :: (helper (ncid+1) k')
    end in helper 0 k.

(* transform H to H^{gad}. H^{gad} = sum_{1<=s<=r} [H_s^{anc} + lambda * V_s] *)
Fixpoint Hgad_helper (nc nht htid k nq : nat) (lambda : R) (hori : lowprog) : lowprog :=
  match hori with 
  | [] => []
  | x :: ax =>
    let termv := mult_ampli_hplus (RtoC lambda) (HV_aterm nht htid k nq x) in
    let term_anc := Hanc_aterm nc nht htid k in
    let aterm := plus_plus_plus termv term_anc in    
    plus_plus_plus aterm (Hgad_helper nc nht (htid+1) k nq lambda ax)
  end.


(* Entry function for generating the Ham with ancilla qubits 
 nq: nquit of program hori *)  
Definition Hgad (k nq : nat) (lambda : R) (hori : lowprog) : lowprog :=
  Hgad_helper nq (length hori) 0 k nq lambda hori. 
