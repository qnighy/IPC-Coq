Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.
Require Import PProp.
Require Import LJ.

(* Russel-Hilbert calculus *)
Inductive HJ_provable(L1:list PProp): PProp -> Prop :=
  | HJ_axiom P1: In P1 L1 -> HJ_provable L1 P1
  | HJ_modus_ponens P1 P2:
      HJ_provable L1 (PPimpl P1 P2) ->
      HJ_provable L1 P1 ->
      HJ_provable L1 P2
  | HJ_K P1 P2:
      HJ_provable L1 (PPimpl P1 (PPimpl P2 P1))
  | HJ_S P1 P2 P3:
      HJ_provable L1
        (PPimpl (PPimpl P1 (PPimpl P2 P3)) (PPimpl (PPimpl P1 P2) (PPimpl P1 P3)))
  | HJ_bot_elim P1:
      HJ_provable L1 (PPimpl PPbot P1)
  | HJ_conj_intro P1 P2:
      HJ_provable L1 (PPimpl P1 (PPimpl P2 (PPconj P1 P2)))
  | HJ_conj_elim_l P1 P2:
      HJ_provable L1 (PPimpl (PPconj P1 P2) P1)
  | HJ_conj_elim_r P1 P2:
      HJ_provable L1 (PPimpl (PPconj P1 P2) P2)
  | HJ_disj_intro_l P1 P2:
      HJ_provable L1 (PPimpl P1 (PPdisj P1 P2))
  | HJ_disj_intro_r P1 P2:
      HJ_provable L1 (PPimpl P2 (PPdisj P1 P2))
  | HJ_disj_elim P1 P2 P3:
      HJ_provable L1
        (PPimpl
          (PPimpl P1 P3)
          (PPimpl
            (PPimpl P2 P3)
            (PPimpl (PPdisj P1 P2) P3))).

Lemma HJ_I:
  forall L1 P1, HJ_provable L1 (PPimpl P1 P1).
Proof.
intros L1 P1.
eapply HJ_modus_ponens.
- eapply HJ_modus_ponens.
  + apply (HJ_S _ P1 (PPimpl P1 P1) P1).
  + apply (HJ_K _ P1 (PPimpl P1 P1)).
- apply (HJ_K _ P1 P1).
Qed.

Lemma HJ_perm:
  forall P1 L1 L2, Permutation L1 L2 -> HJ_provable L1 P1 -> HJ_provable L2 P1.
Proof.
intros P1 L1 L2 HP H.
induction H.
- apply HJ_axiom.
  rewrite <-HP.
  exact H.
- apply (HJ_modus_ponens _ P1); tauto.
- apply HJ_K.
- apply HJ_S.
- apply HJ_bot_elim.
- apply HJ_conj_intro.
- apply HJ_conj_elim_l.
- apply HJ_conj_elim_r.
- apply HJ_disj_intro_l.
- apply HJ_disj_intro_r.
- apply HJ_disj_elim.
Qed.

Lemma HJ_weak:
  forall P1 P2 L1, HJ_provable L1 P1 -> HJ_provable (P2::L1) P1.
Proof.
intros P1 P2 L1 H.
induction H.
- apply HJ_axiom.
  right.
  exact H.
- apply (HJ_modus_ponens _ P1); tauto.
- apply HJ_K.
- apply HJ_S.
- apply HJ_bot_elim.
- apply HJ_conj_intro.
- apply HJ_conj_elim_l.
- apply HJ_conj_elim_r.
- apply HJ_disj_intro_l.
- apply HJ_disj_intro_r.
- apply HJ_disj_elim.
Qed.

Lemma HJ_contr:
  forall P1 P2 L1, HJ_provable (P2::P2::L1) P1 -> HJ_provable (P2::L1) P1.
Proof.
intros P1 P2 L1 H.
induction H.
- apply HJ_axiom.
  destruct H as [H|[H|H]].
  + left; exact H.
  + left; exact H.
  + right; exact H.
- apply (HJ_modus_ponens _ P1); tauto.
- apply HJ_K.
- apply HJ_S.
- apply HJ_bot_elim.
- apply HJ_conj_intro.
- apply HJ_conj_elim_l.
- apply HJ_conj_elim_r.
- apply HJ_disj_intro_l.
- apply HJ_disj_intro_r.
- apply HJ_disj_elim.
Qed.

Lemma HJ_deduction:
  forall P1 P2 L1, HJ_provable (P1::L1) P2 -> HJ_provable L1 (PPimpl P1 P2).
Proof.
intros P1 P2 L1 H.
induction H.
- destruct H as [H|H].
  + rewrite H.
    apply HJ_I.
  + eapply HJ_modus_ponens.
    * apply HJ_K.
    * apply HJ_axiom.
      exact H.
- eapply HJ_modus_ponens.
  + eapply HJ_modus_ponens.
    * apply HJ_S.
    * exact IHHJ_provable1.
  + exact IHHJ_provable2.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_K.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_S.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_bot_elim.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_conj_intro.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_conj_elim_l.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_conj_elim_r.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_disj_intro_l.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_disj_intro_r.
- eapply HJ_modus_ponens.
  + apply HJ_K.
  + apply HJ_disj_elim.
Qed.

Lemma HJ_resolution:
  forall P1 P2 L1, HJ_provable L1 (PPimpl P1 P2) -> HJ_provable (P1::L1) P2.
Proof.
intros P1 P2 L1 H.
eapply HJ_modus_ponens.
- apply HJ_weak.
  exact H.
- apply HJ_axiom.
  apply in_eq.
Qed.

Lemma HJ_deduction_iff:
  forall P1 P2 L1, HJ_provable (P1::L1) P2 <-> HJ_provable L1 (PPimpl P1 P2).
Proof.
intros P1 P2 L1.
split.
- apply HJ_deduction.
- apply HJ_resolution.
Qed.

Lemma LJ_provable_HJ_provable:
  forall P1 L1, LJ_provable L1 P1 -> HJ_provable L1 P1.
Proof.
intros P1 L1 H.
induction H.
- apply (HJ_perm _ L1).
  + exact H.
  + exact IHLJ_provable.
- apply HJ_weak.
  exact IHLJ_provable.
- apply HJ_contr.
  exact IHLJ_provable.
- apply HJ_axiom.
  apply in_eq.
- apply HJ_resolution.
  apply HJ_bot_elim.
- rewrite HJ_deduction_iff in IHLJ_provable2.
  eapply HJ_modus_ponens.
  + apply HJ_weak.
    exact IHLJ_provable2.
  + eapply HJ_modus_ponens.
    * apply HJ_axiom.
      apply in_eq.
    * apply HJ_weak.
      apply IHLJ_provable1.
- revert IHLJ_provable.
  apply HJ_deduction.
- rewrite HJ_deduction_iff in IHLJ_provable.
  rewrite HJ_deduction_iff in IHLJ_provable.
  eapply HJ_modus_ponens.
  + eapply HJ_modus_ponens.
    * apply HJ_weak.
      exact IHLJ_provable.
    * rewrite HJ_deduction_iff.
      apply HJ_conj_elim_r.
  + rewrite HJ_deduction_iff.
    apply HJ_conj_elim_l.
- eapply HJ_modus_ponens.
  + eapply HJ_modus_ponens.
    * apply HJ_conj_intro.
    * exact IHLJ_provable1.
  + exact IHLJ_provable2.
- eapply HJ_modus_ponens.
  + eapply HJ_modus_ponens.
    * eapply HJ_modus_ponens.
      { apply HJ_disj_elim. }
      apply HJ_weak.
      rewrite <-HJ_deduction_iff.
      exact IHLJ_provable1.
    * apply HJ_weak.
      rewrite <-HJ_deduction_iff.
      exact IHLJ_provable2.
  + apply HJ_axiom.
    apply in_eq.
- eapply HJ_modus_ponens.
  + apply HJ_disj_intro_l.
  + exact IHLJ_provable.
- eapply HJ_modus_ponens.
  + apply HJ_disj_intro_r.
  + exact IHLJ_provable.
Qed.

Lemma HJ_provable_LJ_provable:
  forall P1 L1, HJ_provable L1 P1 -> LJ_provable L1 P1.
Proof.
intros P1 L1 H.
induction H.
-
-
-
-
-
-
-
-
-
-
-
Qed.