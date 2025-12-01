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
Definition Hanc_sndq_helper (i j k: nat) : lowprog :=
  let term1 := (RtoC(R1/R2), k, fun _ => paulii) in
  let f := fun idx => (if (Nat.eqb idx i || Nat.eqb idx j) then pauliz else paulii) in
  let term2 := (RtoC(-R1/R2), k, f) in 
  term1 :: term2 :: nil.

(* sum_{1<=i<j}} 1/2(I - Z_i Z_j), sum over i from 1 to j-1 *)
(* j: the last qubit; k: length of one term *)
Fixpoint Hanc_sndq (i j k: nat) : lowprog :=
  match i with
  | 0 => []
  | S n => let term := Hanc_sndq_helper i j k in
  plus_plus_plus term (Hanc_sndq n j k)
  end.


(* sum over j from 2 to k *)
Fixpoint Hanc_fstq (j k : nat) : lowprog :=
  match j with
  | 0 => []
  | 1 => []
  | S n' => let term := Hanc_sndq n' j k in
  plus_plus_plus term (Hanc_fstq n' k) end.

(* H_s^{anc}, add I to make its length n+kr.
nc: number of computational qubits;
nht: r, number of tensor terms; 
htid: 0 to r-1, ternsor term id; 
k: size of the largest term.
*)
Fixpoint Hanc_aterm_helper (pre post : lowprog_ten) (hori : lowprog) : lowprog :=
  match hori with
  | [] => []
  | x :: ax => (ten_ten_ten pre (ten_ten_ten x post)) :: (Hanc_aterm_helper pre post ax)
  end.

(* H_s^{anc} = sum_{1<=i<j} sum_{i<j<=k} [1/2 (I - Z_{s,i} Z_{s,j})] *)
Definition Hanc_aterm (nc nht htid k : nat) : lowprog := 
  let hori : lowprog := Hanc_fstq k k in
  let pre : lowprog_ten := (myC1, nc + htid * k, fun _ => paulii) in 
  let post := (myC1, (nht-htid-1) * k, fun _ => paulii) in 
  Hanc_aterm_helper pre post hori.


(* c_{s,j} sigma_{s,j} X_{s, j} *)
(* nht: r, number of tensor terms; 
  htid: 0 to r-1, ternsor term id; 
  ncid: 0 to nc-1, qubit id in the tensor H^{comp} including I 
  k: size of the largest term;
  kid: the kid_th computation qubit in one tensor term (excluding I).
*)
Definition HV_qcomp (nht htid ncid k kid : nat) (ht : lowprog_ten) : lowprog_ten := 
  match ht with (amp, nc, f) =>
    let id_anc := (nc + htid * k + kid) in
    let cs : C := if kid =? 1 then amp else myC1 in
    let g := fun idx => 
        (if (idx =? ncid) && (Nat.leb ncid nc) then f idx 
          else if idx =? id_anc then paulix 
          else paulii) in
    (cs, nc + k*nht, g)
  end.

(* find the id of the computational qubit starting from curid *)
Fixpoint locate_ncid_aux (fuel nc curid : nat) (f : nat -> paulimat) : nat :=
  match fuel with
  | 0 => nc  (* give up *)
  | S fuel' =>
      if curid =? nc then nc
      else if paulimat_eqb (f curid) paulii
           then locate_ncid_aux fuel' nc (curid + 1) f
           else curid
  end.

Definition locate_ncid (nc curid : nat) (f : nat -> paulimat) : nat :=
  locate_ncid_aux (nc - curid) nc curid f.

(* V = sum_1^k c_{s,j} sigma_{s, j} X_{s, j} *)
Definition HV_aterm (nht htid k : nat) (ht : lowprog_ten) : lowprog := 
  match ht with (amp, nc, f) => 
  let fix helper (curid kid : nat) : lowprog :=
    match kid with
    | 0 => [] (* all k terms already expanded *)
    | S k' => 
      let ncid := locate_ncid nc curid f in   
      (HV_qcomp nht htid ncid k kid ht) :: (helper (ncid+1) k')
    end in helper 0 k
  end.

(* transform H to H^{gad}. H^{gad} = sum_{1<=s<=r} [H_s^{anc} + lambda * V_s] *)
Fixpoint Hgad_helper (nc nht htid k : nat) (lambda : R) (hori : lowprog) : lowprog :=
  match hori with 
  | [] => []
  | x :: ax =>
    let termv := mult_ampli_hplus (RtoC lambda) (HV_aterm nht htid k x) in
    let term_anc := Hanc_aterm nc nht htid k in
    let aterm := plus_plus_plus termv term_anc in    
    plus_plus_plus aterm (Hgad_helper nc nht (htid+1) k lambda ax)
  end.

Definition Hgad (k : nat) (lambda : R) (hori : lowprog) : lowprog :=
  let nht := length hori in
  match hori with 
  | [] => []
  | (_, nc, _) :: ax => Hgad_helper nc nht 0 k lambda hori
  end.
    
  


