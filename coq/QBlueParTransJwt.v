(* Define the JWT *)
Require Import QuantumLib.Matrix.

Require Export QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.


Definition paulimat_eqb (a b : paulimat) : bool :=
  match a, b with
  | paulix, paulix => true
  | pauliy, pauliy => true
  | pauliz, pauliz => true
  | paulii, paulii => true
  | _, _ => false
  end.

Definition app_pauli (s1 s2 : paulimat) : (C * paulimat) :=
  match s1, s2 with
  | paulii, x => (myC1, x)
  | x, paulii => (myC1, x)
  | paulix, paulix => (myC1, paulii)
  | pauliy, pauliy => (myC1, paulii)
  | pauliz, pauliz => (myC1, paulii)
  | paulix, pauliy => (Ci, pauliz)
  | pauliy, paulix => (Copp Ci, pauliz)
  | pauliy, pauliz => (Ci, paulix)
  | pauliz, pauliy => (Copp Ci, paulix)
  | pauliz, paulix => (Ci, pauliy)
  | paulix, pauliz => (Copp Ci, pauliy)
  end.


(* (a x b) x (c x d), all items are tensor *)
Definition ten_ten_ten (m1 m2: nat) (p1 p2: lowprog_ten) : lowprog_ten :=
  let '(z1, f) := p1 in
  let '(z2, g) := p2 in   
  (Cmult z1 z2, fun x => if x <? m1 then f x else g (Nat.sub x m2)). 

(* (a + b) x (c + d) *)
Fixpoint plus_ten_plus (m1 m2: nat) (p1: lowprog) (p2: lowprog) : lowprog := 
  match p1 with [] => p2
  | x::ax => let fix helper (t: lowprog_ten) (tl: lowprog) : lowprog:=
    (match tl with [] => []
    | y::ay => (ten_ten_ten m1 m2 t y) :: (helper t ay) 
    end) in
  (helper x p2) ++ (plus_ten_plus m1 m2 ax p2)
  end.

(* (a x b) o (c x d), left and right must have equal number of terms *)
Definition ten_app_ten_helper (z1 : C) (m: nat) (f: nat -> paulimat) (p2: lowprog_ten) : lowprog_ten :=
  let (z2, g) := p2 in 
    let fix helper (idx : nat) : C * (nat -> paulimat) :=
      let (zz, pp) := app_pauli (f idx) (g idx) in
      match idx with 
      | 0 => (zz, fun x => pp)
      | S m' =>
        let (z_rec, h_rec) := helper m' in
        (Cmult zz z_rec,
        fun x => if x =? idx then pp else h_rec x)
      end
    in
    let (zcom, fcom) := helper m in
    (Cmult z1 (Cmult z2 zcom), fcom).

Definition ten_app_ten (m: nat) (p1 p2: lowprog_ten) : lowprog_ten :=
  let  (z, f) := p1 in
  ten_app_ten_helper z m f p2. 
        
Fixpoint plus_app_plus (m : nat) (p1 p2: lowprog) : lowprog :=
  match p1 with 
  | [] => p2
  | x::ax => let fix helper (a : lowprog_ten) (l : lowprog) : lowprog :=  
    (match l with [] => []
    | b :: bx => (ten_app_ten m a b) :: (helper a bx)
    end) in
  (helper x p2) ++ (plus_app_plus m ax p2)
  end.

Definition plus_plus_plus (p1 p2: lowprog) : lowprog := p1 ++ p2.

Fixpoint plus_app_ten (m : nat) (h1l : lowprog) (h2 : lowprog_ten) : lowprog :=
  match h1l with 
  | [] => []
  | h1 :: rem => (ten_app_ten m h1 h2) :: (plus_app_ten m rem h2) 
  end.

Fixpoint ten_app_plus (m : nat) (h1 : lowprog_ten) (h2l : lowprog) : lowprog :=
  match h2l with 
  | [] => []
  | h2 :: rem => (ten_app_ten m h1 h2) :: (ten_app_plus m h1 rem) 
  end.

(* transformation for boson qubit mapping *)
(* ladder operator *)
(* |0><1| = (+) = 1/2(X+iY) *)
Definition ladder_anni : lowprog :=
  let x := fun n => paulix in
  let y := fun n => pauliy in
  (RtoC (R1/R2), x) :: (Cmult Ci (RtoC (R1/R2)), y) :: nil.

(* |1><0| = (-) = 1/2(X-iY) *)
Definition ladder_creator : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
(RtoC (R1/R2), x) :: (Cmult (-Ci) (RtoC (R1/R2)), y) :: nil.

(* ∣1><1∣= 1/2(I−Z) *)
Definition projector : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (R1/R2), x) :: (Cmult (-myC1) (RtoC (R1/R2)), y) :: nil. 

(* ∣0><0∣= 1/2(I+Z) *)
Definition projector0 : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (R1/R2), x) :: (RtoC (R1/R2), y) :: nil. 


(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Fixpoint mult_ampli_hplus (z : C) (p : lowprog) : lowprog :=
  match p with [] => []
  | x :: ax => ((Cmult z (fst x)), (snd x)) :: (mult_ampli_hplus z ax)
  end.  


(* arXiv:2307.06580v. Eq. 34-36 *)
(* boson binary mapping *)
(* convert a number to binary. n: natural number; len: list of the binary number *)
Fixpoint cnt2bin (n len : nat) : list nat :=
  match len with
  | 0 => []
  | S n' => (cnt2bin (Nat.div n 2) n') ++ [n mod 2]
  end.
(* Compute cnt2bin 9 5. *) (* 01001 *)

(* map |0><1| to lowprog *)
Definition unitstate2pauli (n1 n2 : nat) : lowprog :=
  match n1, n2 with 
  | 0, 0 => projector0 
  | 0, 1 => ladder_anni 
  | 1, 0 => ladder_creator 
  | 1, 1 => projector
  | _, _ => []
  end.

(* map |n1><n2| to lowprog. *)
Fixpoint state2pauli_helper (n1 n2 : list nat) : lowprog :=
  match n1, n2 with 
  | x::ax, y::ay => plus_plus_plus (unitstate2pauli x y) (state2pauli_helper ax ay)
  | [], _ => []
  | _, [] => []
  end.

Definition state2pauli (n1 n2 Nq : nat) : lowprog :=
  let n1l := cnt2bin n1 Nq in
  let n2l := cnt2bin n2 Nq in
  state2pauli_helper n1l n2l.


(* Nb: max capacity of a bosonic site *)  
Definition boson_creator (Nb : nat) : lowprog :=
  let Nq := Nat.log2_up (Nb + 1) in
  let nterm : nat := ((Nat.pow 2 Nq) - 1)%nat in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (sqrt (INR (n))) in
      let aterm := mult_ampli_hplus amp (state2pauli n n' Nq) in
      plus_plus_plus aterm (helper n')
    end in
  helper nterm.

Definition boson_annihilator (Nb : nat) : lowprog :=
  let Nq := Nat.log2_up (Nb + 1) in
  let nterm : nat := ((Nat.pow 2 Nq) - 1)%nat in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (sqrt (INR (n))) in
      let aterm := mult_ampli_hplus amp (state2pauli n' n Nq) in
      plus_plus_plus aterm (helper n')
    end in
  helper nterm.

Definition boson_numerator (Nb : nat) : lowprog :=
  let Nq := Nat.log2_up (Nb + 1) in 
  let nterm : nat := Nat.pow 2 Nq in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (INR n) in
      let aterm := mult_ampli_hplus amp (state2pauli n' n' Nq) in
      plus_plus_plus aterm (helper n') 
    end in
  helper nterm.


(* The following method are based on onehot. Not used. To be consistent with fermion *)  
(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
(* Nb: max number of boson particles in one site *)
Definition boson_creator_bin (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (sqrt (INR (n) + R1)) in
    let nleft := n in
    let nright := Nat.sub Nb (Nat.add n 1) in
    let left : lowprog := [(myC1, fun x => paulii)] in
    let right : lowprog := [(myC1, fun x => paulii)] in 
    let mid : lowprog := (plus_ten_plus 1%nat 1%nat ladder_anni ladder_creator) in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_ten_plus (nleft + 1%nat) nright (plus_ten_plus nleft 1%nat left mid1) right 
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => term 0%nat
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb =? 0 then [] else helper (Nat.sub Nb 1).

(* b_i = SUM_{1 to Nb} sqrt(n) I_0 x ... x (-)_(n-1) x (+)_(n) ... x I_Nb *)
Definition boson_annihilator_bin (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (sqrt (INR n)) in
    let nleft := Nat.sub n 1 in
    let nright := Nat.sub Nb n in 
    let left : lowprog := [(myC1, fun _ => paulii)] in
    let right : lowprog := [(myC1, fun _ => paulii)] in
    let mid : lowprog := plus_ten_plus 1 1 ladder_creator ladder_anni in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_ten_plus (nleft + 1) nright (plus_ten_plus nleft 1 left mid1) right
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => []
    | 1 => term 1%nat
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb <? 1 then [] else helper Nb.
  
(* n_i = SUM_{0 to Nb} n_i I_0 x ... |1><1|_ni ... x I_Nb *)
Definition boson_numerator_bin (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (INR n) in
    let nleft := n in
    let nright := Nat.sub Nb n in
    let left : lowprog := [(myC1, fun _ => paulii)] in
    let right : lowprog := [(myC1, fun _ => paulii)] in
    let mid : lowprog := mult_ampli_hplus amp projector in
    plus_ten_plus (nleft + 1) nright (plus_ten_plus nleft 1 left mid) right
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => term 0 %nat
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb <? 0 then [] else helper Nb.


(*************** Transform blueExp to lowprog. Another pass is highprog -> lowprog ************)
Local Open Scope nat_scope.
(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n, only apply z to the sites of fermion *)
(* n: # bits; idx: idx_th bit is apply by the ladder op; (idx-1) bits from 0th are applied I/Z;
  par: the particle type of each site *)
Definition fermion_zop (p : option particle) : paulimat :=
  match p with 
  | Some Fem => pauliz
  | _ => paulii (* Bos or None; NOTE to check length of par list is long enough so it never will be None *)
  end.

Definition fermion_creator (n idx : nat) (par : list particle) : lowprog :=
  let nleft := idx in
  let nright := (n - idx - 1)%nat in
  let left : lowprog := [(myC1, fun k => fermion_zop (nth_error par k))] in
  let right : lowprog := [(myC1, fun _ => paulii)] in
  plus_ten_plus nleft (nright+1)%nat left (plus_ten_plus 1%nat nright ladder_creator right).


Definition fermion_anni (n idx : nat) (par : list particle) : lowprog :=
  let nleft := idx in
  let nright := (n - idx - 1)%nat in
  let left : lowprog := [(myC1, fun k => fermion_zop (nth_error par k))] in
  let right : lowprog := [(myC1, fun _ => paulii)] in
  plus_ten_plus nleft (nright+1)%nat left (plus_ten_plus 1%nat nright ladder_anni right).


(* Get the number of qubits in each site. *)
Definition get_nqbit_bexp_unit (input : particle) : nat :=
  match input with
  | Bos n => Nat.log2_up (n+1)
  | Fem => 1
  end.

Fixpoint get_nqbit_bexp (input :iota) : list nat :=
  match input with
  | [] => []
  | x :: ax => (get_nqbit_bexp_unit x) :: get_nqbit_bexp ax
  end.

(* count the number of qubits before and after the target site *)
Fixpoint sum_pre_qubits (input : list nat) (sid : nat) : nat :=
  match input, sid with
  | [], _ => 0
  | _, 0 => 0
  | x :: xs, S sid' => x + sum_pre_qubits xs sid'
  end.

Fixpoint sum_post_qubits (input : list nat) (sid : nat) : nat :=
  match input, sid with
  | [], _ => 0
  | _ :: xs, 0 => fold_left Nat.add xs 0%nat
  | _ :: xs, S sid' => sum_post_qubits xs sid'
  end.

(* Compute sum_pre_qubits [3; 5; 2; 7] 1.
Compute sum_post_qubits [3; 5; 2; 7] 1. *)

(* Transform a creator / annhialator / ID. *)
Definition bexp_map_hunit
  (sid : nat) (* sid: its site id. *)
  (qbits : list nat) (* qbits: # of qubits in each site. *)
  (par : iota) (* particle type of each site *)
  (flag : nat) (* flag: 0: anni, 1: creator, 2: id *)
  : lowprog :=
  let nleft   := sum_pre_qubits  qbits sid in
  let nright  := sum_post_qubits qbits sid in
  let IDten := [(myC1, fun _ => paulii)] in
  match nth_error par sid with
  | Some (Bos nb) =>
      let nq := Nat.log2_up (nb + 1) in (* nq: @ of bits for (Bos nb) type *)
      match flag with
      | 0%nat =>
          plus_ten_plus (nleft + nq) nright (plus_ten_plus nleft nq IDten (boson_annihilator nb)) IDten
      | 1%nat =>
          plus_ten_plus (nleft + nq) nright (plus_ten_plus nleft nq IDten (boson_creator nb)) IDten
      | _ => IDten
      end

  | Some Fem =>
      match flag with
      (* position id (from 0th) of nleft is applied ladder op *)
      | 0%nat => fermion_anni (nleft + 1 + nright)%nat nleft par
      | 1%nat => fermion_creator (nleft + 1 + nright)%nat nleft par 
      | _ => IDten
      end

  | _ => []
  end.


(* Count the # of sites corresponding to this blueExp *)
Fixpoint count_sites (input : blueExp) : nat :=
  match input with
  | HId | HAnni => 1
  | HDag e => count_sites e
  | HPlus e1 e2 => count_sites e1
  | HTensor e1 e2 => (count_sites e1) + (count_sites e2)
  | HApp e1 e2 => count_sites e1
  end. 

(* helper func to transform blueExp to lowprog *)
Fixpoint bexp_map (input : blueExp) (qbits : list nat) (par : list particle)
  (st_id : nat) : lowprog :=
  match input with
  | HId => bexp_map_hunit st_id qbits par 2
  | HAnni => bexp_map_hunit st_id qbits par 0
  | HDag x => match x with
    | HAnni => bexp_map_hunit st_id qbits par 1
    | _ => []
    end
  | HPlus e1 e2 => plus_plus_plus (bexp_map e1 qbits par st_id) (bexp_map e2 qbits par st_id)
  | HApp e1 e2 => 
    let par1 := skipn st_id qbits in
    let nsite := count_sites e1 in 
    let nq := sum_pre_qubits par1 nsite in (* calculate the qubits of this exp *)
    plus_app_plus nq (bexp_map e1 qbits par st_id) (bexp_map e2 qbits par st_id)
  
  | HTensor e1 e2 =>
    let par1 := skipn st_id qbits in
    let nsite1 := count_sites e1 in
    let nq1 := sum_pre_qubits par1 nsite1 in
    let par2 := skipn nsite1 par1 in
    let nsite2 := count_sites e2 in 
    let nq2 := sum_pre_qubits par2 nsite2 in
    plus_ten_plus nq1 nq2 (bexp_map e1 qbits par st_id) (bexp_map e2 qbits par (st_id + nsite1))
  end.


(* Transform from blueExp to lowprog *)
Definition bexp_to_lowprog (input : blueExp) (input_type : iota) : lowprog :=
  let qbits := get_nqbit_bexp input_type in
  bexp_map input qbits input_type 0%nat.
(*************** Another pass to transform blueExp to lowprog. End. ************)



(* Transform state from high to low level (described in binary).
  len: # of the sites of input; 
  input: nat-based ket; input_type: Fem/(Bos m) for particle types since sid.
  output: list nat, the bin-based ket; iota: change all particle types to (Bos 2). *)
Fixpoint state_map_basis_helper (len : nat) (input : basisKet) (input_type : iota) : 
  ((list nat) * iota) := 
  match input_type with 
  | [] => ([], [])
  | ty::aty => 
    let sid := Nat.sub len (length input_type) in
    let (ket_app, ty_app) := state_map_basis_helper len input aty in
    let klen : nat := 
      (match ty with
      | Fem => 1%nat
      | Bos m => Nat.log2_up m 
      end) in 
    let newk : (list nat) := cnt2bin (input sid) klen in
    let newt : iota := repeat (Bos 2) klen in
    (newk ++ ket_app, newt ++ ty_app)
  end.

Definition state_map_basis (input_wamp : C * basisKet) (input_type : iota) : (C * basisKet) := 
  let (amp, input) := input_wamp in
  let (bin_ket, _) := state_map_basis_helper (length input_type) input input_type in
  let output := fun x => nth x bin_ket 0%nat in
  (amp, output).

Definition state_map (input : psi) (input_type : iota) : psi :=
  map (fun x => state_map_basis x input_type) input.

Fixpoint state_type_bin (input : iota) : iota :=
  match input with 
  | [] => []
  | ty :: ty_app => 
    let klen : nat := 
      (match ty with
      | Fem => 1%nat
      | Bos m => Nat.log2_up m 
      end) in 
      let newt := repeat (Bos 2) klen in
      newt ++ (state_type_bin ty_app)
  end.


(*************** Transform highprog to lowprog. ************)
(* Currently this pass require the form e1 + e2, e1 := e3 tensor e4, e3 := e5 app e6, e5 := anni | creator | hunit.
If this high level will be used later, need to debug *)
(*
(* Jordan-Wigner transformation for fermions 
Quantum chemistry beyond Born-Oppenheimer approximation by Libor Veis Eq 17-18 *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n, only apply z to the sites of fermion *)
(* idx: position of the bit of ladder op; apply Z (same fermion)/I (other) to bits before it; 
n: total bits;
par: the particle type of each site *)

(* Get the number of qubits in each site. *)
Definition get_nqbit_hsnd (input : hsnd) : nat :=
  match input with
  | anni (Bos n) | creator (Bos n) | hunit (Bos n) => n
  | anni Fem | creator Fem | hunit Fem => 2
  end.


Fixpoint get_nqbit_ten (len : nat) (f : nat -> list hsnd) : list nat :=
  match len with 
  | 0 => []
  | S n => match (f n) with 
    | [] => [] (* no snd in this site *)
    | x :: ax => (* e1 o e2 ... o en *)
    (get_nqbit_hsnd x) :: (get_nqbit_ten n f)
    end
  end.

Definition get_nqbit (input : highprog) : list nat :=
  match input with 
  | [] => []
  | (_, len, f) :: ax => get_nqbit_ten len f (* just take the first one to get the nqubits *)
  end.

(* Get the particle type of each site. *)
Definition get_particle_vs_site_hsnd (input : hsnd) : particle :=
  match input with 
    | anni p | creator p | hunit p => p
  end.

Fixpoint get_particle_vs_site_ten (len : nat) (f : nat -> list hsnd) : list particle :=
  match len with 
  | 0 => []
  | S n => match (f n) with 
    | [] => [] (* no snd in this site *)
    | x :: ax => (* e1 o e2 ... o en *)
    (get_particle_vs_site_hsnd x) :: (get_particle_vs_site_ten n f)
    end
  end.

Definition get_particle_vs_site (input : highprog) : list particle :=
  match input with 
  | [] => []
  | (_, len, f) :: ax => get_particle_vs_site_ten len f
  end.


(* Transform a creator / annhialator. sid: its site id. qbits: # of qubits in each site *)
Definition snd_map_h0 (input : hsnd) (sid : nat) (qbits : list nat) 
  (par : list particle) : lowprog := 
  let nleft := sum_pre_qubits qbits sid in
  let nright := sum_post_qubits qbits sid in
  let IDten := [(myC1, fun x => paulii)] in 
  match input with 
  | anni (Bos Nb) => plus_ten_plus (nleft+Nb)%nat nright 
    (plus_ten_plus nleft Nb IDten (boson_annihilator Nb)) IDten 
  | creator (Bos Nb) => plus_ten_plus (nleft+Nb)%nat nright 
    (plus_ten_plus nleft Nb IDten (boson_creator Nb)) IDten 
  | anni Fem => fermion_anni (nleft + nright + 2)%nat sid par
  | creator Fem => fermion_creator (nleft + nright + 2)%nat sid par
  | hunit Fem => [(myC1, fun x => paulii)]
  | hunit (Bos Nb) => [(myC1, fun x => paulii)]
  end.

(* transform e1 o e2 *)
Fixpoint snd_map_h1 (sid : nat) (input : list hsnd) (qbits : list nat) 
  (par : list particle) : lowprog := 
  match input with [] => []
    | x :: ax => plus_app_plus (fold_left Nat.add qbits 0%nat)
     (snd_map_h0 x sid qbits par) (snd_map_h1 sid ax qbits par) 
  end.

(* transform e1 x e2 *)
Definition snd_map_h2 (input : highprog_ten) (qbits : list nat) 
  (par : list particle) : lowprog := 
  match input with (z, m, f) =>
  let fix helper (id: nat) : lowprog :=
    match id with 0 => []
    | S m' => plus_ten_plus (snd_map_h1 id (f id) qbits par) (helper m')
    end
    in mult_ampli_hplus z (helper m)
  end.

(* transform e1 + e2 *)
Fixpoint snd_map_h3 (input : list highprog_ten) (qbits : list nat) 
  (par : list (option particle)) : lowprog :=
  match input with 
  | [] => []
  | x :: ax => plus_plus_plus (snd_map_h2 x qbits par) (snd_map_h3 ax qbits par)
  end.

(* Transform from high program to low *)
Definition snd_map (input : highprog) : lowprog :=
  let qubits := get_nqbit input in
  let particle := get_particle_vs_site input in
  snd_map_h3 input qubits particle.
(*************** Transform highprog to lowprog. End. ************)
*)
