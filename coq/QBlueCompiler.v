(* Define the JWT, Lie-Trotter fomular *)
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QBlue.QBlueSyntax.
Local Open Scope nat_scope.

Require Import List.
Import ListNotations.


(* Pauli string *)
Inductive paulimat: Type :=
| paulix             (* X = [[0;1]; [1;0] ] *)
| pauliy             (* Y = [[0;-i]; [i;0]] *)
| pauliz             (* Z = [[1;0]; [0;-1]] *)
| paulii.

(* lowprog_ten: (amplitude, length, f: index -> element *)
Definition lowprog_ten := (C * nat * (nat -> paulimat)) %type.
Definition lowprog := list lowprog_ten.

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
Definition ladder_anni : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
  [(RtoC (1/2), 1%nat, x); (Cmult Ci (RtoC (1/2)), 1%nat, y)].

Definition ladder_creator : lowprog :=
  let x := fun x => paulix in
  let y := fun x => pauliy in
[(RtoC (1/2), 1%nat, x); (Cmult (-Ci) (RtoC (1/2)), 1%nat, y)].

(* ∣1⟩⟨1∣= 1/2(I−Z) *)
Definition projector : lowprog :=
  let x := fun x => paulii in
  let y := fun x => pauliz in
[(RtoC (1/2), 1%nat, x); (Cmult (-C1) (RtoC (1/2)), 1%nat, y)]. 


(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Fixpoint mult_ampli_hplus (z : C) (p : lowprog) : lowprog :=
  let helper (t : lowprog_ten) : lowprog_ten := 
    match t with (z1, m, f) => (Cmult z z1, m, f) end in
  match p with [] => []
  | x :: ax => (helper x) :: (mult_ampli_hplus z ax)
  end.

(* b_i^+ = SUM_{0 to Nb-1} sqrt(n+1) I_0 x ... x (+)_n x (-)_(n+1) ... x I_Nb *)
Definition boson_creator (Nb : nat) : lowprog :=
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
Definition boson_annihilator (Nb : nat) : lowprog :=
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
Definition boson_numerator (Nb : nat) : lowprog :=
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


(* Jordan-Wigner transformation for fermions *)
(* a_n^+ = Z_1 x Z_2 ... Z_n-1 x (-)_n *)
Definition fermion_creator (n : nat) : lowprog :=
  let left : lowprog := [(C1, Nat.sub n 1, fun _ => pauliz)] in
  plus_ten_plus left ladder_creator.

Definition fermion_anni (n : nat) : lowprog :=
  let left : lowprog := [(C1, Nat.sub n 1, fun _ => pauliz)] in
  plus_ten_plus left ladder_anni.
  
(* Transform highprog to lowprog. *)
(* Get the number of qubits in each site. *)
Definition get_nqbit_hsnd (input : hsnd) : nat :=
  match input with 
    | creator _ Nb => Nb 
    | anni _ Nb => Nb  
    | hunit Nb => Nb
  end.

Fixpoint get_nqbit_ten (len : nat) (f : nat -> list hsnd) : list nat :=
  match len with 
  | 0 => []
  | S n => match (f n) with 
    | [] => [] (* no snd in this site *)
    | x :: ax => (* e1 o e2 ... o en, just take the first one to get the nqubits *)
    (get_nqbit_hsnd x) :: (get_nqbit_ten n f)
    end
  end.

Definition get_nqbit (input : highprog) : list nat :=
  match input with 
  | [] => []
  | (_, len, f) :: ax => get_nqbit_ten len f
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
Definition snd_map_h0 (input : hsnd) (sid : nat) (qbits : list nat) : lowprog := 
  let prebits := sum_pre_qubits qbits sid in
  let postbits := sum_post_qubits qbits sid in
  let left := [(C1, prebits, fun x => paulii)] in 
  let right := [(C1, postbits, fun x => paulii)] in 
  match input with 
  | anni bos Nb => plus_ten_plus (plus_ten_plus left (boson_annihilator Nb)) right 
  | creator bos Nb => plus_ten_plus (plus_ten_plus left (boson_creator Nb)) right 
  | anni fermi Nb => plus_ten_plus (fermion_anni sid) right
  | creator fermi Nb => plus_ten_plus (fermion_creator sid) right
  | hunit Nb => (
    let mid := [(C1, Nb, fun x => paulii)] in
    plus_ten_plus (plus_ten_plus left mid) right)
  end.

(* transform e1 o e2 *)
Fixpoint snd_map_h1 (sid : nat) (input : list hsnd) (qbits : list nat) : lowprog :=
  match input with [] => []
    | x :: ax => plus_app_plus (snd_map_h0 x sid qbits) (snd_map_h1 sid ax qbits) end.

(* transform e1 x e2 *)
Definition snd_map_h2 (input : highprog_ten) (qbits : list nat) : lowprog :=
  match input with (z, m, f) =>
  let fix helper (id: nat) : lowprog :=
    match id with 0 => []
    | S m' => plus_ten_plus (snd_map_h1 id (f id) qbits) (helper m')
    end
    in mult_ampli_hplus z (helper m)
  end.

(* transform e1 + e2 *)
Fixpoint snd_map_h3 (input : list highprog_ten) (qbits : list nat) : lowprog :=
  match input with 
  | [] => []
  | x :: ax => plus_plus_plus (snd_map_h2 x qbits) (snd_map_h3 ax qbits)
  end.

(* Transform from high program to low *)
Definition snd_map (input : highprog) : lowprog :=
  let qubits := get_nqbit input in
  snd_map_h3 input qubits.
  

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
(* exp(-iHt) *)
Parameter expH : C -> lowprog -> lowprog.


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
    | h :: ht => plus_app_plus (expH (Cmult (-Ci) t) [h]) (e_split t ht)
    end.

(* theorem: Tight error bound for the first-order Lie-Trotter formula *)
(* A Theory of Trotter Error, by Andrew M. Childs etc *)
Theorem lie_trotter_error_bound :
  forall (t : R) (hlist : lowprog),
  let approx := e_split t hlist in
  let gold := expH (Cmult (-Ci) t) hlist in
  Rle (norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)))
    (trotter_error_bound t hlist).

Proof. Admitted.


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

Theorem suzuki_second_order_error_bound :
  forall (t : R) (hlist : lowprog),
  let approx := e_split_suzuki t hlist in
  let gold := expH (Cmult (-Ci) t) hlist in
  Rle (norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)))
      (suzuki_error_bound t hlist).

Proof. Admitted.


(* Qdrift trotterization *)
(* Random sampling *)
Parameter A : Type.
Parameter L : list A.            
Parameter L1 : list A.
Parameter Lwei : list R. (* weight/strength of each term *)     
Parameter Prob : A -> R.

Axiom length_match :
  length L = length Lwei.

Axiom weighted_prob :
  forall (i : nat) (xi : A),
    nth_error L i = Some xi ->
    nth_error Lwei i = Some (Prob xi).

Fixpoint count_occurrences (x : A) (L : list A) : nat :=
  match L with
  | [] => 0
  | y :: ys =>
      if x =? y then 1 + count_occurrences x ys
      else count_occurrences x ys
  end.

Definition frequency_in (x : A) (L : list A) : R :=
  let count := count_occurrences x L in
  let total := length L in
  if Nat.eqb total 0 then 0
  else (INR count) / (INR total).

Axiom randome_sampling :
  forall x : A,
    In x L1 ->
    In x L /\ (* Every sampled element must come from L *)
    (* follow the probability distribution *)
    frequency_in x L1 = Prob x / fold_right Rplus 0 P.


Theorem qdrift_error : 
 forall n rho, qdrift_sample rho L = P 
 -> (forall P, P in L' => pick rho L := P)
 -> size of L' = n 
 -> exp(-i L' t) <=
Proof.
  
Qed.



