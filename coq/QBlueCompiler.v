(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSemantics.
Require Import QBlue.QBlueType.
Local Open Scope R_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

From SQIR Require Import SQIR.

Definition paulimat_eqb (a b : paulimat) : bool :=
  match a, b with
  | paulix, paulix => true
  | pauliy, pauliy => true
  | pauliz, pauliz => true
  | paulii, paulii => true
  | _, _ => false
  end.

(* This is for trotterization. Maybe need to modify later *)
(* exp(-i t H) *)
Parameter expH : R -> lowprog -> lowprog.

(* This is the input for sythesization *)
Definition ugate := (R * lowprog) %type.
Parameter exp_ugate : R -> lowprog -> ugate. (* exp(-i r H) *)

Definition app_pauli (s1 s2 : paulimat) : (C * paulimat) :=
  match s1, s2 with
  | paulii, x => (C1, x)
  | x, paulii => (C1, x)
  | paulix, paulix => (C1, paulii)
  | pauliy, pauliy => (C1, paulii)
  | pauliz, pauliz => (C1, paulii)
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
  (RtoC (1/2), 1%nat, x) :: (Cmult Ci (RtoC (1/2)), 1%nat, y) :: nil.

(* |1><0| = (-) = 1/2(X-iY) *)
Definition ladder_creator : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
(RtoC (1/2), 1%nat, x) :: (Cmult (-Ci) (RtoC (1/2)), 1%nat, y) :: nil.

(* ∣1><1∣= 1/2(I−Z) *)
Definition projector : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (1/2), 1%nat, x) :: (Cmult (-C1) (RtoC (1/2)), 1%nat, y) :: nil. 

(* ∣0><0∣= 1/2(I+Z) *)
Definition projector0 : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
(RtoC (1/2), 1%nat, x) :: (RtoC (1/2), 1%nat, y) :: nil. 


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
    | S n' => let amp := RtoC (sqrt (INR (n + 1))) in
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
    let amp := RtoC (sqrt (INR (n + 1))) in
    let left : lowprog := [(C1, n, fun x => paulii)] in
    let right : lowprog := [(C1, Nat.sub Nb (Nat.add n 1), fun x => paulii)] in 
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
    let left : lowprog := [(C1, Nat.sub n 1, fun _ => paulii)] in
    let right : lowprog := [(C1, Nat.sub Nb n, fun _ => paulii)] in
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
    let left : lowprog := [(C1, n, fun _ => paulii)] in
    let right : lowprog := [(C1, Nat.sub Nb n, fun _ => paulii)] in
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
  | Some Fermi => (C1, 1%nat, fun _ => pauliz)
  | _ => (C1, 1%nat, fun _ => paulii)
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
  let left := [(C1, prebits, fun x => paulii)] in 
  let right := [(C1, postbits, fun x => paulii)] in 
  match input with 
  | anni (Bos Nb) => plus_ten_plus (plus_ten_plus left (boson_annihilator Nb)) right 
  | creator (Bos Nb) => plus_ten_plus (plus_ten_plus left (boson_creator Nb)) right 
  | anni Fem => plus_ten_plus (fermion_anni sid par) right
  | creator Fem => plus_ten_plus (fermion_creator sid par) right
  | hunit Fem => (
    let mid := [(C1, 2%nat, fun x => paulii)] in
    plus_ten_plus (plus_ten_plus left mid) right)
  | hunit (Bos Nb) => (
    let mid := [(C1, Nb, fun x => paulii)] in
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
 

(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator_tt (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-C1)%C [ten_app_ten h2 h1]).

Definition commutator_st (h1 : lowprog) (h2 : lowprog_ten) : lowprog :=
  let l1 := plus_app_ten h1 h2 in
  let l2 := mult_ampli_hplus (-C1) (ten_app_plus h2 h1) in
  plus_plus_plus l1 l2.

Definition commutator_ts (h1 : lowprog_ten) (h2 : lowprog) : lowprog :=
  let l1 := ten_app_plus h1 h2 in
  let l2 := mult_ampli_hplus (-C1) (plus_app_ten h2 h1) in
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
  let l2 := mult_ampli_hplus (-C1) (plus_app_plus h2 h1) in
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



(* Qdrift trotterization *)
(* Definition of L: a matrix. It relies on Hamiltonian H. It operates on the state |phi><phi| *)
(* L(rho) = i(H rho - rho H). This matrix takes rho and do commutation i[H, rho] *)
Variable nd : nat. 
Definition TransL := Matrix nd nd.
Parameter L_h : list R. (* hj *)
Parameter L_Lori : list TransL. (* Lj *)           
Parameter L_sampledID : list nat. (* Sampled IDs. if L1 = [1,3,3,2], chose L[3] twice *)
(* Diamond norm, the sum of singular values in the space with ancilla qubits considered. *)
Parameter norm_diamond : TransL -> R.
(* Transform L to exp(tL). *)
Parameter expH1 : R -> TransL -> TransL.

(* Require each Lj to have a strength hj *)
Axiom length_match :
  length L_sampledID = length L_h.

Definition lambda : R := fold_right Rplus 0%R L_h.

(* Theorem for qdrift. *)
(* calculate L = sum_j (hj Lj) *)
Fixpoint sum_L (prob : list R) (ll : list TransL) : TransL :=
  match prob, ll with 
  | [], _ => Zero
  | _, [] => Zero
  | p :: pl, m :: ml => Mplus (scale p m) (sum_L pl ll) 
  end.

Definition tau (t : R) : R := lambda * t / (INR (length L_sampledID)).

(* Generate the sampled list based on the sampled ID idl and the original list vl. *)
Fixpoint sum_sampled_exp (t : R) (idl : list nat) : TransL :=
  match idl with
  | [] => Zero
  | id :: ax =>
    match (nth_error L_Lori id, nth_error L_h id) with
    | (None, _) => Zero
    | (_, None) => Zero
    | (Some Lj, Some hj) => Mplus (scale (hj / lambda) (expH1 (tau t) Lj)) (sum_sampled_exp t ax)
    end
  end.

Definition qdrift_error (t : R) :=   
  let N : R := INR (length L_sampledID) in
  let gold := expH1 (t / N) (sum_L L_h L_Lori) in
  let approx := sum_sampled_exp t L_sampledID in
  0.5 * (norm_diamond (Mplus gold (-1 .* approx))).


Local Open Scope nat_scope.

(* perturbative gadgtization *)
(* Define H^gad. *)
(* 1/2(I - Z_i Z_j) *)
(* i: any qubit before j; j: the last qubit; k: length of one term *)
Definition Hanc_sndq_helper (i j k: nat) : lowprog :=
  let term1 := (RtoC(1/2), k, fun _ => paulii) in
  let f := fun idx => (if (Nat.eqb idx i || Nat.eqb idx j) then pauliz else paulii) in
  let term2 := (RtoC(-1/2), k, f) in 
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
  let pre : lowprog_ten := (C1, nc + htid * k, fun _ => paulii) in 
  let post := (C1, (nht-htid-1) * k, fun _ => paulii) in 
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
    let cs : C := if kid =? 1 then amp else C1 in
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
  let f := (fun id => if (inb Nat.eqb id reg) then p else paulii) in (C1, nbit, f).

Local Close Scope nat_scope.

(* H = exp(-i pi/4 X) exp(-i pi/4 Z) exp(-i pi/4 X). For IBM *)
(* H unitary gate on X and Z basis.
   nbit: # of bits in circuit; qid: id of the current bit *)
Definition H_u (nbit qid : nat) : list ugate := 
  let xu := exp_ugate (PI/4) [fill_pl nbit [qid] paulix] in
  let zu := exp_ugate (PI/4) [fill_pl nbit [qid] pauliz] in
  xu :: zu :: xu :: nil. 

(* S = exp(-i pi/4 Z) *)
Definition S_u (nbit qid : nat) : list ugate := 
  let zu := exp_ugate (PI/4) [fill_pl nbit [qid] pauliz] in zu :: nil.

(* S^+ = exp(-i 7 pi/4 Z) *)
Definition SDag_u (nbit qid : nat) : list ugate := 
  let zu := exp_ugate (7 * PI/4) [fill_pl nbit [qid] pauliz] in zu :: nil. 

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


(*************** Transform blueExp to lowprog. Another pass is highprog -> lowprog ************)
Local Open Scope nat_scope.
(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n, only apply z to the sites of fermion *)
(* n: apply Z/I to the first n sites; par: the particle type of each site *)
Definition fermion_zop_helper1 (p : particle) : lowprog_ten :=
  match p with 
  | Fem => (C1, 1%nat, fun _ => pauliz)
  | _ => (C1, 1%nat, fun _ => paulii)
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
  let left   := [(C1, preb,  fun _ => paulii)] in
  let right  := [(C1, postb, fun _ => paulii)] in
  match nth_error par sid with
  | Some (Bos nb) =>
      match flag with
      | 0%nat =>
          plus_ten_plus (plus_ten_plus left (boson_annihilator nb)) right
      | 1%nat =>
          plus_ten_plus (plus_ten_plus left (boson_creator nb)) right
      | _ =>
          let mid := [(C1, nb, fun _ => paulii)] in
          plus_ten_plus (plus_ten_plus left mid) right
      end

  | Some Fem =>
      match flag with
      | 0%nat =>
          plus_ten_plus (fermion_anni1 sid par) right
      | 1%nat =>
          plus_ten_plus (fermion_creator1 sid par) right
      | _ =>
          let mid := [(C1, 2%nat, fun _ => paulii)] in
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



Local Close Scope nat_scope.
(*************** Transform blueExp to lowprog. ************)


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
