(* Do synthesization upon different hardware *)

Require Import QBlue.QBlueUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueParTransJwt.


(* exp(-i r H) *)
Definition exp_ugate (t : R) (lp_ten : nat -> paulimat) : ugate :=
  (t, lp_ten).


(* 2. to gates of IBM analog, X, Z, ZZ gates *)
(* fill_pl 3 2 X => I tensor I tensor X *)
Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if eqb x a then true else inb eqb a xs
  end.

Definition fill_pl (reg : list nat) (p : paulimat) : (nat -> paulimat) :=
  let f := (fun id => if (inb Nat.eqb id reg) then p else paulii) in f.


(* H = exp(-i pi/4 X) exp(-i pi/4 Z) exp(-i pi/4 X). For IBM *)
(* H unitary gate on X and Z basis.
   nbit: # of bits in circuit; qid: id of the current bit *)
Definition H_u (qid : nat) : list ugate := 
  let xu := exp_ugate (PI/R4) (fill_pl [qid] paulix) in
  let zu := exp_ugate (PI/R4) (fill_pl [qid] pauliz) in
  xu :: zu :: xu :: nil. 

(* S = exp(-i pi/4 Z) *)
Definition S_u (qid : nat) : list ugate := 
  let zu := exp_ugate (PI/R4) (fill_pl [qid] pauliz) in zu :: nil.

(* S^+ = exp(-i 7 pi/4 Z) *)
Definition SDag_u (qid : nat) : list ugate := 
  let zu := exp_ugate (R7 * PI/R4) (fill_pl [qid] pauliz) in zu :: nil. 

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
    let hu := H_u m in
    let su := S_u m in 
    let sdagu := SDag_u m in
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
    let mid := exp_ugate t (fill_pl ml pauliz) in
    let (left, right) := synth_analog_ibm_helper ml nbit pauli_str in
    left ++ [mid] ++ right
  else [].

Fixpoint syn_analog_indiana_x' (nbit:nat) (f : nat -> paulimat) : nat -> paulimat :=
  match nbit with
    0 => fun _ => paulii
  | S m => if is_i (f m) 
           then syn_analog_indiana_x' m f 
           else fun i => if i =? m then paulix else syn_analog_indiana_x' m f i
  end.
Definition syn_analog_indiana_x (t:R) (nbit:nat) (f : nat -> paulimat) : ugate :=
    (t, syn_analog_indiana_x' nbit f).


(* Helper: builds result without repeated ++ on growing acc *)
Fixpoint syn_analog_indiana_a_dl (nbit:nat) (f : nat -> paulimat)
  (accf : list ugate -> list ugate) : (list ugate -> list ugate) :=
  match nbit with
  | 0 => accf
  | S m =>
    match f m with
    | pauliy =>
      let left := (Rdiv PI R4, (fun i => if i =? m then pauliz else paulii)) in
      let right := (Rdiv (Rmult R7 PI) R4, (fun i => if i =? m then pauliz else paulii)) in
      syn_analog_indiana_a_dl m f (fun tl => left :: (accf (right :: tl)))
    | pauliz =>
      let v1 := (Rdiv PI R4, (fun i => if i =? m then paulix else paulii)) in
      let v2 := (Rdiv PI R4, (fun i => if i =? m then pauliz else paulii)) in
      syn_analog_indiana_a_dl m f
        (fun tl => v1 :: v2 :: v1 :: (accf (v1 :: v2 :: v1 :: tl)))
    | _ => syn_analog_indiana_a_dl m f accf
    end
  end.

Definition syn_analog_indiana_a (nbit:nat) (f : nat -> paulimat) (acc: list ugate) : list ugate :=
  syn_analog_indiana_a_dl nbit f (fun tl => rev_append (rev acc) tl) [].

Definition synth_analog_indiana_single (t : R) (nbit : nat) (f : nat -> paulimat) : list ugate :=
  syn_analog_indiana_a nbit f [syn_analog_indiana_x t nbit f].

Definition synth_analog_indiana (t:R) (nbit:nat) (input : lowprog) : list ugate :=
  rev (fold_left (fun acc b =>
    rev_append (synth_analog_indiana_single (Rmult t (fst (fst b))) nbit (snd b)) acc) input []).

(*
Fixpoint syn_analog_indiana_a (nbit:nat) (f : nat -> paulimat) (acc: list ugate) : list ugate :=
  match nbit with 
    0 => acc
  | S m => 
     match f m with 
       pauliy => 
          syn_analog_indiana_a m f 
            ((Rdiv PI R4, (fun i => if i =? m then pauliz else paulii))
                ::acc++[((Rdiv (Rmult R7 PI) R4), (fun i => if i =? m then pauliz else paulii))])
       | pauliz => 
          let v := (Rdiv PI R4, fun i => if i =? m then paulix else paulii)
                      ::(Rdiv PI R4, fun i => if i =? m then pauliz else paulii)
                      ::(Rdiv PI R4, fun i => if i =? m then paulix else paulii)::[] in
          syn_analog_indiana_a m f (v++acc++v)
       | _ => syn_analog_indiana_a m f acc
      end
   end.


Definition synth_analog_indiana (t:R) (nbit:nat) (input : lowprog) : list ugate :=
  fold_left (fun a b => synth_analog_indiana_single (Rmult t (fst (fst b))) nbit (snd b)::a) input [].
*)


