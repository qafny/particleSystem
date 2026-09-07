(* Correctness for digital synthesization (paper's Algorithm 1 / Lemma 4.3).
   The previous version of this file targeted an algorithm
   (helper_digital_ibm_ulist) that no longer exists -- QBlueSynthDigital.v was
   rewritten to a different construction (find_last_abit / cvt_all /
   abit_cx_all) and the old algorithm is now commented out there. This file
   is a from-scratch proof against the current algorithm, not a resync of
   the old one.

   Scope so far: the single-qubit, Z-only base case (paper's Figure 8,
   exp(-itZ) = RZ(2t)), proved up to global phase. NOT yet covered: X and Y
   (need the basis-change gates' own matrix semantics -- H and the
   U1(pi/2)-then-H combo), and the multi-qubit case (the CX-ladder's parity
   correctness). See the TODO at the bottom for what's still needed. *)

Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Pad.
Require Import QuantumLib.Proportional.
From SQIR Require Import SQIR ExtractionGateSet UnitarySem UnitaryOps.

Require Import QBlue.QBlueProofUtility.
Require Import QBlue.QBlueSyntax.
Require Import QBlue.QBlueSynthDigital.

Module EG := ExtractionGateSet.

(* Generic SQIR/ExtractionGateSet facts not already available as lemmas in
   the imported libraries -- reusable for the X/Y/multi-qubit cases too. *)

Lemma uc_eval_useq : forall dim u1 u2,
  EG.uc_eval dim (EG.useq u1 u2) = Mmult (EG.uc_eval dim u2) (EG.uc_eval dim u1).
Proof. intros. reflexivity. Qed.

Lemma uc_eval_U1_1qubit : forall a : R,
  EG.uc_eval 1 (EG.U1 a 0) = rotation 0 0 a.
Proof.
  intros a.
  unfold EG.uc_eval, EG.U1.
  cbn [EG.to_base_ucom].
  unfold SQIR.U1.
  unfold UnitarySem.uc_eval, ueval_r.
  unfold pad_u, pad.
  simpl.
  rewrite kron_1_l; auto with wf_db.
  rewrite kron_1_r.
  reflexivity.
Qed.

Lemma uc_eval_SKIP_1qubit : EG.uc_eval 1 EG.SKIP = I 2.
Proof.
  unfold EG.SKIP, EG.ID.
  rewrite uc_eval_U1_1qubit.
  exact I_rotation.
Qed.

(* EG.uc_eval dim (invert u) = (EG.uc_eval dim u)† for well-formed u --
   combines EG.invert_same (EG-level invert matches base-level invert) with
   UnitaryOps.invert_correct (base-level invert is the adjoint), neither of
   which is stated at the EG level directly. *)
Lemma uc_eval_invert : forall dim u, well_formed u ->
  EG.uc_eval dim (EG.invert u) = (EG.uc_eval dim u) †.
Proof.
  intros dim u Hwf.
  rewrite (EG.invert_same dim u Hwf).
  unfold EG.uc_eval.
  symmetry. apply invert_correct.
Qed.

(* Single-qubit, Z-only case. *)

Definition f_z : nat -> paulimat := fun _ => pauliz.

(* For a lone Z (no basis conversion needed, no other qubits to ladder CX
   from), the "half" circuit collapses to three SKIPs. *)
Lemma half_z_shape :
  EG.useq (cvt_all 1 f_z) (abit_cx_all 0 0 f_z)
  = EG.useq (EG.useq EG.SKIP EG.SKIP) EG.SKIP.
Proof. reflexivity. Qed.

Lemma half_z_is_id : EG.uc_eval 1 (EG.useq (cvt_all 1 f_z) (abit_cx_all 0 0 f_z)) = I 2.
Proof.
  rewrite half_z_shape.
  rewrite uc_eval_useq, uc_eval_useq, uc_eval_SKIP_1qubit.
  repeat rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma wf_half_z : well_formed (EG.useq (cvt_all 1 f_z) (abit_cx_all 0 0 f_z)).
Proof.
  rewrite half_z_shape.
  repeat constructor.
Qed.

(* Lemma 4.3, single-qubit Z case: the circuit synth_digital_ibm_apauli
   produces is the same unitary as expH t Z, up to a global phase.
   (Global phase, not literal equality, because SQIR's U1(a) = diag(1, e^ia)
   differs from the paper's Figure 8 RZ(2t) = diag(e^-it, e^it) by exactly
   that -- a standard, physically unobservable discrepancy.) *)
Theorem synth_z_1qubit_correct : forall t : R,
  expH 2 t (lowprogten2mat C1 1 f_z) ∝ EG.uc_eval 1 (synth_digital_ibm_apauli t 1 f_z).
Proof.
  intros t.
  assert (Hgen: lowprogten2mat C1 1 f_z = σz).
  { simpl. rewrite Mscale_1_l. apply kron_1_r. }
  rewrite Hgen, expH_Z.
  cbn [synth_digital_ibm_apauli find_last_abit is_i f_z].
  rewrite uc_eval_useq, uc_eval_useq.
  rewrite (uc_eval_invert 1 _ wf_half_z).
  rewrite half_z_is_id, uc_eval_U1_1qubit.
  rewrite id_adjoint_eq.
  rewrite Mmult_1_l, Mmult_1_r; auto with wf_db.
  exists (-t)%R.
  assert (H0: (0/2)%R = 0%R) by lra.
  unfold rotation, scale.
  rewrite H0, cos_0, sin_0, Cexp_0.
  apply functional_extensionality; intro x.
  apply functional_extensionality; intro y.
  destruct x as [|[|x]], y as [|[|y]]; try lca.
  rewrite Cmult_1_r, <- Cexp_add. f_equal. unfold QBlueUtility.R2. ring.
Qed.

(* TODO to extend Lemma 4.3's proof beyond this base case:
   1. X and Y, single qubit: need EG.uc_eval of EG.H (the Hadamard gate) and
      of the U1(pi/2)-then-H combination that cvt2base uses for Y, matched
      against expH_X / expH_Y (added alongside expH_Z in
      QBlueProofUtility.v). Same technique as above (unfold to base SQIR
      semantics, reduce pad_u/kron_1_l/r, compute the resulting 2x2 matrix),
      just more trig to push through.
   2. Multi-qubit: needs the CX-ladder (abit_cx_all) to actually be proved to
      compute the right parity -- i.e. that conjugating the U1 rotation by
      the ladder correctly implements the multi-qubit tensor-product
      Pauli exponential, not just the single-qubit rotation. This is the
      genuinely new content Algorithm 1 adds over the single-qubit case, and
      hasn't been attempted yet. *)
