(* Define the unitilies, including numbers etc *)
Require Import Reals.
Require Export QuantumLib.Complex.
From QBlue Require Import QBlueSyntax.

(* Define the utility functions, including ceil, random generator, etc. *)

Definition paulimat_eqb (a b : paulimat) : bool :=
  match a, b with
  | paulix, paulix => true
  | pauliy, pauliy => true
  | pauliz, pauliz => true
  | paulii, paulii => true
  | _, _ => false
  end.

Definition mult_r_hplus (r : R) (lp : lowprog) : lowprog :=
  map (fun p => let '(x, f) := p in
  let z : C := ((r * (fst x)) %R, (r * (snd x)) %R) in (z, f)) lp.

(* norm_prog analog of mult_r_hplus: scaling a real-amplitude Hamiltonian by
   a real scalar is just real multiplication, no complex-pair bookkeeping. *)
Definition mult_r_normprog (r : R) (np : norm_prog) : norm_prog :=
  map (fun p => let '(amp, f) := p in ((r * amp)%R, f)) np.

(* Bridging conversions between lowprog (C amplitude) and norm_prog (R
   amplitude) -- needed at the boundary where norm_prog-based code (e.g.
   QBlueTrotter.v) is wired into lowprog-based code (e.g. the particle
   transformation output / QBlueSynth's input) in QBlueCompile.v.
   lowprog2norm_prog takes the real part of each amplitude; every Hamiltonian
   this project actually constructs has real coefficients (paper's
   Definition 3.1), so this is exact in practice, not an approximation --
   but it's not statically enforced by lowprog's type, so this conversion
   silently drops any imaginary part a malformed lowprog might have. *)
Definition lowprog2norm_prog (lp : lowprog) : norm_prog :=
  map (fun p => let '(z, f) := p in (fst z, f)) lp.

Definition norm_prog2lowprog (np : norm_prog) : lowprog :=
  map (fun p => let '(amp, f) := p in (RtoC amp, f)) np.


Definition R2 : R := R1 + R1.
Definition R4 : R := R1 + R1 + R1 + R1.
Definition R7 : R := R1 + R2 + R4.

Parameter ceilR_N: R -> nat. 

(* get the smaller Real value *)
Parameter Rltb : R -> R -> bool.
Parameter Reqb : R -> R -> bool.

(* Random generator, given a max bound r, return uniformly from [0, r)*)
Parameter random_float : R -> R.

(* factorial *)
Fixpoint factor (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * factor k
  end.

Fixpoint Cpow (c : C) (n : nat) : C :=
  match n with
  | O   => C1
  | S k => c * Cpow c k
  end.

