(* Define the JWT *)
Require Import QuantumLib.Quantum.
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
Definition ten_ten_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  let '(z1, m, f) := p1 in
  let '(z2, n, g) := p2 in   
  (Cmult z1 z2, Nat.add m n, fun x => if x <? m then f x else g (Nat.sub x m)). 

(* (a + b) x (c + d) *)
Fixpoint plus_ten_plus (p1: lowprog) (p2: lowprog) : lowprog := 
  match p1 with [] => p2
  | x::ax => let fix helper (t: lowprog_ten) (tl: lowprog) : lowprog:=
    (match tl with [] => []
    | y::ay => (ten_ten_ten t y) :: (helper t ay) 
    end) in
  (helper x p2) ++ (plus_ten_plus ax p2)
  end.

(* (a x b) o (c x d), left and right must have equal number of terms *)
Definition ten_app_ten_helper (z1 : C) (m: nat) (f: nat -> paulimat) (p2: lowprog_ten) : lowprog_ten :=
  match p2 with (z2, m, g) => (* p2 must have the same length as m. *)
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
    (Cmult z1 (Cmult z2 zcom), m, fcom)
  end.

Definition ten_app_ten (p1 p2: lowprog_ten) : lowprog_ten :=
  match p1 with
  | (z, m, f) => ten_app_ten_helper z m f p2
  end.
        
Fixpoint plus_app_plus (p1 p2: lowprog) : lowprog :=
  match p1 with [] => p2
  | x::ax => let fix helper (a : lowprog_ten) (l : lowprog) : lowprog :=  
    (match l with [] => []
    | b :: bx => (ten_app_ten a b) :: (helper a bx)
    end) in
  (helper x p2) ++ (plus_app_plus ax p2)
  end.

Definition plus_plus_plus (p1 p2: lowprog) : lowprog := p1 ++ p2.

Fixpoint plus_app_ten (h1l : lowprog) (h2 : lowprog_ten) : lowprog :=
  match h1l with 
  | [] => []
  | h1 :: rem => (ten_app_ten h1 h2) :: (plus_app_ten rem h2) 
  end.

Fixpoint ten_app_plus (h1 : lowprog_ten) (h2l : lowprog) : lowprog :=
  match h2l with 
  | [] => []
  | h2 :: rem => (ten_app_ten h1 h2) :: (ten_app_plus h1 rem) 
  end.

(* transformation for boson qubit mapping *)
(* ladder operator *)
(* |0><1| = (+) = 1/2(X+iY) *)
Definition ladder_anni : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
  (RtoC (R1/R2), 1%nat, x) :: (Cmult Ci (RtoC (R1/R2)), 1%nat, y) :: nil.

(* |1><0| = (-) = 1/2(X-iY) *)
Definition ladder_creator : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
(RtoC (R1/R2), 1%nat, x) :: (Cmult (-Ci) (RtoC (R1/R2)), 1%nat, y) :: nil.

(* ∣1><1∣= 1/2(I−Z) *)
Definition projector : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (R1/R2), 1%nat, x) :: (Cmult (-myC1) (RtoC (R1/R2)), 1%nat, y) :: nil. 

(* ∣0><0∣= 1/2(I+Z) *)
Definition projector0 : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (R1/R2), 1%nat, x) :: (RtoC (R1/R2), 1%nat, y) :: nil. 


(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Fixpoint mult_ampli_hplus (z : C) (p : lowprog) : lowprog :=
  let helper (t : lowprog_ten) : lowprog_ten := 
    match t with (z1, m, f) => (Cmult z z1, m, f) end in
  match p with [] => []
  | x :: ax => (helper x) :: (mult_ampli_hplus z ax)
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

Definition boson_creator (Nb : nat) : lowprog :=
  let nterm : nat := Nat.sub (Nat.pow 2 Nb) 2 in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (sqrt (INR (n+1))) in
      let aterm := mult_ampli_hplus amp (state2pauli (Nat.add n 1) n Nb) in
      plus_plus_plus aterm (helper n') 
    end in
  helper nterm.

Definition boson_annihilator (Nb : nat) : lowprog :=
  let nterm : nat := Nat.sub (Nat.pow 2 Nb) 2 in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (sqrt (INR (n + 1))) in
      let aterm := mult_ampli_hplus amp (state2pauli n (Nat.add n 1) Nb) in
      plus_plus_plus aterm (helper n') 
    end in
  helper nterm.

Definition boson_numerator (Nb : nat) : lowprog :=
  let nterm : nat := Nat.sub (Nat.pow 2 Nb) 1 in
  let fix helper (n : nat) :=
    match n with 
    | 0 => []
    | S n' => let amp := RtoC (INR n) in
      let aterm := mult_ampli_hplus amp (state2pauli n n Nb) in
      plus_plus_plus aterm (helper n') 
    end in
  helper nterm.


(* The following method are based on onehot. Not used. To be consistent with fermion *)  
(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Definition boson_creator_bin (Nb : nat) : lowprog :=
  let term (n : nat) : lowprog :=
    let amp := RtoC (sqrt (INR (n) + R1)) in
    let left : lowprog := [(myC1, n, fun x => paulii)] in
    let right : lowprog := [(myC1, Nat.sub Nb (Nat.add n 1), fun x => paulii)] in 
    let mid : lowprog := (plus_ten_plus ladder_anni ladder_creator) in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_plus_plus (plus_plus_plus left mid1) right 
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
    let left : lowprog := [(myC1, Nat.sub n 1, fun _ => paulii)] in
    let right : lowprog := [(myC1, Nat.sub Nb n, fun _ => paulii)] in
    let mid : lowprog := plus_ten_plus ladder_creator ladder_anni in
    let mid1 : lowprog := mult_ampli_hplus amp mid in
    plus_ten_plus (plus_ten_plus left mid1) right
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
    let left : lowprog := [(myC1, n, fun _ => paulii)] in
    let right : lowprog := [(myC1, Nat.sub Nb n, fun _ => paulii)] in
    let mid : lowprog := mult_ampli_hplus amp projector in
    plus_ten_plus (plus_ten_plus left mid) right
  in
  let fix helper (n : nat) : lowprog :=
    match n with
    | 0 => term 0 %nat
    | S k => plus_plus_plus (term n) (helper k)
    end
  in if Nb <? 0 then [] else helper Nb.


(*************** Transform highprog to lowprog. ************)
(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n, only apply z to the sites of fermion *)
(* n: apply Z/I to the first n sites; par: the particle type of each site *)
Definition fermion_zop_helper (p : option particle) : lowprog_ten :=
  match p with 
  | Some Fermi => (myC1, 1%nat, fun _ => pauliz)
  | _ => (myC1, 1%nat, fun _ => paulii)
  end.

(* get [Z, I]^{ten (n-1)} *)
Fixpoint fermion_zop (n : nat) (par : list (option particle)) : lowprog :=
  match n, par with 
  | 0, _ => [] 
  | _, [] => []
  | S n', x :: ax => (fermion_zop_helper x) :: (fermion_zop n' ax)
  end.

Definition fermion_creator (n : nat) (par : list (option particle)) : lowprog :=
  let left : lowprog := fermion_zop (Nat.sub n 1) par in
  plus_ten_plus left ladder_creator.

Definition fermion_anni (n : nat) (par : list (option particle)) : lowprog :=
  let left : lowprog := fermion_zop (Nat.sub n 1) par in
  plus_ten_plus left ladder_anni.
 

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
Definition get_particle_vs_site_hsnd (input : hsnd) : option particle :=
  match input with 
    | anni p | creator p | hunit p => Some p
   
  end.

Fixpoint get_particle_vs_site_ten (len : nat) (f : nat -> list hsnd) : list (option particle) :=
  match len with 
  | 0 => []
  | S n => match (f n) with 
    | [] => [] (* no snd in this site *)
    | x :: ax => (* e1 o e2 ... o en *)
    (get_particle_vs_site_hsnd x) :: (get_particle_vs_site_ten n f)
    end
  end.

Definition get_particle_vs_site (input : highprog) : list (option particle) :=
  match input with 
  | [] => []
  | (_, len, f) :: ax => get_particle_vs_site_ten len f
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

(* Transform a creator / annhialator. sid: its site id. qbits: # of qubits in each site *)
Definition snd_map_h0 (input : hsnd) (sid : nat) (qbits : list nat) 
  (par : list (option particle)) : lowprog := 
  let prebits := sum_pre_qubits qbits sid in
  let postbits := sum_post_qubits qbits sid in
  let left := [(myC1, prebits, fun x => paulii)] in 
  let right := [(myC1, postbits, fun x => paulii)] in 
  match input with 
  | anni (Bos Nb) => plus_ten_plus (plus_ten_plus left (boson_annihilator Nb)) right 
  | creator (Bos Nb) => plus_ten_plus (plus_ten_plus left (boson_creator Nb)) right 
  | anni Fem => plus_ten_plus (fermion_anni sid par) right
  | creator Fem => plus_ten_plus (fermion_creator sid par) right
  | hunit Fem => (
    let mid := [(myC1, 2%nat, fun x => paulii)] in
    plus_ten_plus (plus_ten_plus left mid) right)
  | hunit (Bos Nb) => (
    let mid := [(myC1, Nb, fun x => paulii)] in
    plus_ten_plus (plus_ten_plus left mid) right) 
  end.

(* transform e1 o e2 *)
Fixpoint snd_map_h1 (sid : nat) (input : list hsnd) (qbits : list nat) 
  (par : list (option particle)) : lowprog := 
  match input with [] => []
    | x :: ax => plus_app_plus (snd_map_h0 x sid qbits par) (snd_map_h1 sid ax qbits par) end.

(* transform e1 x e2 *)
Definition snd_map_h2 (input : highprog_ten) (qbits : list nat) 
  (par : list (option particle)) : lowprog := 
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



(*************** Transform blueExp to lowprog. Another pass is highprog -> lowprog ************)
Local Open Scope nat_scope.
(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n, only apply z to the sites of fermion *)
(* n: apply Z/I to the first n sites; par: the particle type of each site *)
Definition fermion_zop_helper1 (p : particle) : lowprog_ten :=
  match p with 
  | Fem => (myC1, 1%nat, fun _ => pauliz)
  | _ => (myC1, 1%nat, fun _ => paulii)
  end.

(* get [Z, I]^{ten (n-1)} *)
Fixpoint fermion_zop1 (n : nat) (par : list particle) : lowprog :=
  match n, par with 
  | 0%nat, _ => [] 
  | _, [] => []
  | S n', x :: ax => (fermion_zop_helper1 x) :: (fermion_zop1 n' ax)
  end.

Definition fermion_creator1 (n : nat) (par : list particle) : lowprog :=
  let left : lowprog := fermion_zop1 (Nat.sub n 1) par in
  plus_ten_plus left ladder_creator.

Definition fermion_anni1 (n : nat) (par : list particle) : lowprog :=
  let left : lowprog := fermion_zop1 (Nat.sub n 1) par in
  plus_ten_plus left ladder_anni.
 

(* Get the number of qubits in each site. *)
Definition get_nqbit_bexp_unit (input : particle) : nat :=
  match input with
  | Bos n => n
  | Fem => 2
  end.

Fixpoint get_nqbit_bexp (input :iota) : list nat :=
  match input with
  | [] => []
  | x :: ax => (get_nqbit_bexp_unit x) :: get_nqbit_bexp ax
  end.


(* Transform a creator / annhialator / ID. *)
Definition bexp_map_hunit
  (sid : nat) (* sid: its site id. *)
  (qbits : list nat) (* qbits: # of qubits in each site. *)
  (par : iota) (* particle type of each site *)
  (flag : nat) (* flag: 0: anni, 1: creator, 2: id *)
  : lowprog :=
  let preb   := sum_pre_qubits  qbits sid in
  let postb  := sum_post_qubits qbits sid in
  let left   := [(myC1, preb,  fun _ => paulii)] in
  let right  := [(myC1, postb, fun _ => paulii)] in
  match nth_error par sid with
  | Some (Bos nb) =>
      match flag with
      | 0%nat =>
          plus_ten_plus (plus_ten_plus left (boson_annihilator nb)) right
      | 1%nat =>
          plus_ten_plus (plus_ten_plus left (boson_creator nb)) right
      | _ =>
          let mid := [(myC1, nb, fun _ => paulii)] in
          plus_ten_plus (plus_ten_plus left mid) right
      end

  | Some Fem =>
      match flag with
      | 0%nat =>
          plus_ten_plus (fermion_anni1 sid par) right
      | 1%nat =>
          plus_ten_plus (fermion_creator1 sid par) right
      | _ =>
          let mid := [(myC1, 2%nat, fun _ => paulii)] in
          plus_ten_plus (plus_ten_plus left mid) right
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
  | HApp e1 e2 => plus_app_plus (bexp_map e1 qbits par st_id) (bexp_map e2 qbits par st_id) 
  | HTensor e1 e2 => 
    let nsite := count_sites e1 in
    plus_ten_plus (bexp_map e1 qbits par st_id) (bexp_map e2 qbits par (st_id + nsite))
  end.

(* Transform from blueExp to lowprog *)
Definition bexp_to_lowprog (input : blueExp) (input_type : iota) : lowprog :=
  let qbits := get_nqbit_bexp input_type in
  bexp_map input qbits input_type 0%nat.
(*************** Another pass to transform blueExp to lowprog. End. ************)


(*********** Transform lowprog into Matrix. Needed for proving Hermitian **************)
Definition pauli2mat (p : paulimat) : Square 2 :=
  match p with
  | paulix => σx 
  | pauliy => σy 
  | pauliz => σz 
  | paulii => I 2 
  end.

(* get exp(-i t H) from t, H.
n: # of paulimat in one pauli string *)  
Fixpoint lowprogten2mat (amp : C) (n : nat) (f: nat->paulimat) : Matrix (2^n) (2^n) :=
  match n with
  | 0 => scale amp (I 1)
  | S n' => kron (pauli2mat (f n')) (lowprogten2mat amp n' f)
  end.

Fixpoint lowprog2mat (ham : lowprog) (n : nat) : Matrix (2^n) (2^n) :=
  match ham with
  | [] => I (2^n)
  | (amp, _, f) :: hx =>
      Mplus (lowprogten2mat amp n f) (lowprog2mat hx n)
  end.

Definition is_hermitian_mat {n : nat} (M : Matrix n n) : Prop :=
  M † = M.

Definition is_hermitian_lowprog (H : lowprog) (n : nat) : Prop :=
  is_hermitian_mat (lowprog2mat H n).
(*
Record HermitianLowprog := {
  Hlp        : lowprog;
  Hlp_hermitian : is_hermitian_lowprog Hlp;
}. *)

(*********** Transform lowprog into Matrix. **************)


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


