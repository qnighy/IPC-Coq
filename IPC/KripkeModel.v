Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.
Require Import PProp.
Require Import LJ.

Record KripkeFrame : Type :=
  {
    KF_worlds: Set;
    KF_accesible: relation KF_worlds;
    KF_inhabited: inhabited KF_worlds;
    KF_refl: reflexive _ KF_accesible;
    KF_trans: transitive _ KF_accesible
  }.

Record KripkeModel : Type := 
  {
    KM_frame: KripkeFrame;
    KM_interp_atom: KF_worlds KM_frame -> nat -> bool;
    KM_persistent_atom:
      forall(W1 W2:KF_worlds KM_frame), KF_accesible _ W1 W2 ->
        forall A:nat, KM_interp_atom W1 A = true -> KM_interp_atom W2 A = true
  }.

Fixpoint KM_interp(k:KripkeModel) (W: KF_worlds (KM_frame k)) (P:PProp):Prop :=
  match P with
  | PPbot => False
  | PPatom A => KM_interp_atom k W A = true
  | PPimpl P1 P2 =>
      forall(W': KF_worlds (KM_frame k)),
        KF_accesible _ W W' ->
          KM_interp k W' P1 -> KM_interp k W' P2
  | PPconj P1 P2 => KM_interp k W P1 /\ KM_interp k W P2
  | PPdisj P1 P2 => KM_interp k W P1 \/ KM_interp k W P2
  end.

Lemma KM_persistent:
  forall(k:KripkeModel) (W1 W2:KF_worlds (KM_frame k)),
    KF_accesible (KM_frame k) W1 W2 ->
      forall P:PProp,
        KM_interp k W1 P -> KM_interp k W2 P.
Proof.
intros k W1 W2 HA P H.
revert k W1 W2 HA H.
induction P.
- intros k W1 W2 HA H.
  contradict H.
- intros k W1 W2 HA H.
  revert HA n H.
  apply KM_persistent_atom.
- intros k W1 W2 HA H.
  intros W' HW' H'.
  apply H.
  + revert HA HW'.
    apply KF_trans.
  + exact H'.
- intros k W1 W2 HA H.
  destruct H as (H1,H2).
  split.
  + revert HA H1.
    apply IHP1.
  + revert HA H2.
    apply IHP2.
- intros k W1 W2 HA H.
  destruct H as [H|H].
  + left.
    revert HA H.
    apply IHP1.
  + right.
    revert HA H.
    apply IHP2.
Qed.

Lemma LJ_KM_sound:
  forall L1 P1, LJ_provable L1 P1 ->
    forall k:KripkeModel,
      forall(W:KF_worlds (KM_frame k)),
        (forall P, In P L1 -> KM_interp k W P) ->
        KM_interp k W P1.
Proof.
intros KL1 KP1 HPr k.
induction HPr.
- intros W Hinterp.
  specialize (IHHPr W).
  apply IHHPr.
  intros P HP.
  apply Hinterp.
  rewrite <-H.
  exact HP.
- intros W Hinterp.
  specialize (IHHPr W).
  apply IHHPr.
  intros P HP.
  apply Hinterp.
  right.
  exact HP.
- intros W Hinterp.
  specialize (IHHPr W).
  apply IHHPr.
  intros P HP.
  apply Hinterp.
  destruct HP as [HP|[HP|HP]].
  + left; exact HP.
  + left; exact HP.
  + right; exact HP.
- intros W Hinterp.
  apply Hinterp.
  left.
  reflexivity.
- intros W Hinterp.
  exfalso.
  apply (Hinterp PPbot).
  left.
  reflexivity.
- intros W Hinterp.
  apply IHHPr2.
  intros P [HP|HP].
  + rewrite <-HP.
    apply (Hinterp (PPimpl P1 P2)).
    * left; reflexivity.
    * apply KF_refl.
    * apply IHHPr1.
      intros P' HP'.
      apply Hinterp.
      right.
      exact HP'.
  + apply Hinterp.
    right.
    exact HP.
- intros W Hinterp.
  intros W' HW' H'.
  apply IHHPr.
  intros P [HP|HP].
  + rewrite <-HP.
    exact H'.
  + apply KM_persistent with (W1:=W).
    * exact HW'.
    * apply Hinterp.
      exact HP.
- intros W Hinterp.
  apply IHHPr.
  intros P [HP|[HP|HP]].
  + rewrite <-HP.
    exact (proj1 (Hinterp _ (in_eq _ _))).
  + rewrite <-HP.
    exact (proj2 (Hinterp _ (in_eq _ _))).
  + apply Hinterp.
    right.
    exact HP.
- intros W Hinterp.
  split.
  + apply IHHPr1.
    exact Hinterp.
  + apply IHHPr2.
    exact Hinterp.
- intros W Hinterp.
  destruct (Hinterp _ (in_eq _ _)) as [H|H].
  + apply IHHPr1.
    intros P [HP|HP].
    * rewrite <-HP.
      exact H.
    * apply Hinterp.
      right.
      exact HP.
  + apply IHHPr2.
    intros P [HP|HP].
    * rewrite <-HP.
      exact H.
    * apply Hinterp.
      right.
      exact HP.
- intros W Hinterp.
  left.
  apply IHHPr.
  exact Hinterp.
- intros W Hinterp.
  right.
  apply IHHPr.
  exact Hinterp.
Qed.


Lemma LJ_KM_complete:
  forall L1 P1,
    (forall k:KripkeModel,
      forall(W:KF_worlds (KM_frame k)),
        (forall P, In P L1 -> KM_interp k W P) ->
        KM_interp k W P1) ->
    LJ_provable L1 P1.
Proof.
Qed.