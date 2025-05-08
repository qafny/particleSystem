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
(* Fixpoint get_nqbit (input : list hsnd) : list nat :=
  match input with [] => []
  | x :: ax => 
    match x with 
    | creator (_, Nb) => Nb :: (get_nqbit ax)
    | anni (_, Nb) => Nb :: (get_nqbit ax) end
  end. *)

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
  | anni (bos, Nb) => plus_ten_plus (plus_ten_plus left (boson_annihilator Nb)) right 
  | creator (bos, Nb) => plus_ten_plus (plus_ten_plus left (boson_creator Nb)) right 
  | anni (fermi, Nb) => plus_ten_plus (fermion_anni sid) right
  | creator (fermi, Nb) => plus_ten_plus (fermion_creator sid) right
  end.

(* transform e1 o e2 *)
Fixpoint snd_map_h1 (input : list (nat * hsnd)) (qbits : list nat) : lowprog :=
  match input with [] => []
    | (sid, x) :: ax => plus_app_plus (snd_map_h0 x sid qbits) (snd_map_h1 ax qbits) end.

(* transform e1 x e2 *)
Definition snd_map_h2 (input : highprog_ten) (qbits : list nat) : lowprog :=
  match input with (z, m, f) =>
  let fix helper (id: nat) : lowprog :=
    match id with 0 => []
    | S m' => plus_ten_plus (snd_map_h1 (f id) qbits) (helper m')
    end
    in mult_ampli_hplus z (helper m)
  end.

(* transform e1 + e2 *)
Fixpoint snd_map_h3 (input : list highprog_ten) (qbits : list nat) : lowprog :=
  match input with 
  | [] => []
  | x :: ax => plus_plus_plus (snd_map_h2 x qbits) (snd_map_h3 ax qbits)
  end.

Definition snd_map (input : highprog) : lowprog :=
  let (qubits, progl) := input in
  snd_map_h3 progl qubits.
  

(* The error bound for the Lie-Trotter *)
(* Commutator: [A, B] = AB - BA *)
Definition commutator (h1 h2 : lowprog_ten) : lowprog :=
  [ten_app_ten h1 h2] ++ (mult_ampli_hplus (-C1)%C [ten_app_ten h2 h1]).

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


(* sum_{γ2=γ1+1}^Γ [H_{γ2}, H_{γ1}] *)
Fixpoint comm_sums_helper (h2l : lowprog) (h1 : lowprog_ten) : lowprog :=
  match h2l with 
  | [] => []
  | h2 :: rem => plus_plus_plus (commutator h2 h1) (comm_sums_helper rem h1) 
  end.

Definition comm_sums (gamma1 : nat) (hlist : lowprog) : lowprog :=
  let subl := drop_nth gamma1 hlist in
  match subl with 
  | [] => []
  | h :: rem => comm_sums_helper rem h
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

(* theorem: Tight error bound for the  rst-order Lie-Trotter formula *)
Theorem lie_trotter_error_bound :
  forall (t : R) (hlist : lowprog),
  let approx := e_split t hlist in
  let gold := expH (Cmult (-Ci) t) hlist in
  Rle (norm (plus_plus_plus approx (mult_ampli_hplus (-C1) gold)))
    (trotter_error_bound t hlist).

Proof. Admitted.


