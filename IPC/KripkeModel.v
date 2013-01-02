Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.
Require Import PProp.
Require Import LJ.
Require Import LJm.

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
    KM_interp_atom: KF_worlds KM_frame -> nat -> Prop;
    KM_persistent_atom:
      forall(W1 W2:KF_worlds KM_frame), KF_accesible _ W1 W2 ->
        forall A:nat, KM_interp_atom W1 A -> KM_interp_atom W2 A
  }.

Fixpoint KM_interp(k:KripkeModel) (W: KF_worlds (KM_frame k)) (P:PProp):Prop :=
  match P with
  | PPbot => False
  | PPatom A => KM_interp_atom k W A
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

Program Definition SaturatedUnprovableSequents :  KripkeModel
  :=
{|
  KM_frame := {|
    KF_worlds := { Ant : list PProp & { Suc | LJm_unprovable_saturated Ant Suc } };
    KF_accesible := fun W1 W2 =>
        exists L1, Permutation (L1++projT1 W1) (projT1 W2)
  |};
  KM_interp_atom := fun W A1 => In (PPatom A1) (projT1 W)
|}.
Next Obligation.
destruct (LJm_saturate nil nil) as (L1,(L2,H)).
{
  rewrite <-LJ_LJm_iff.
  apply LJ_consistent.
}
exists.
exists (L1++nil).
exists (L2++nil).
exact H.
Qed.
Next Obligation.
intros (Ant1,(Suc1,H1)).
exists nil.
reflexivity.
Qed.
Next Obligation.
intros (Ant1,(Suc1,H1)) (Ant2,(Suc2,H2)) (Ant3,(Suc3,H3)) (LA,HA) (LB,HB).
exists (LA++LB).
rewrite <-HB,<-HA.
perm.
Qed.
Next Obligation.
simpl in * |- *.
rewrite <-H1.
rewrite in_app_iff.
right.
exact H0.
Qed.

Lemma SUS_Lem:
  forall P1 W,
    (In P1 (projT1 W) ->
        KM_interp SaturatedUnprovableSequents W P1) /\
    (In P1 (proj1_sig (projT2 W)) ->
        ~KM_interp SaturatedUnprovableSequents W P1).
Proof.
induction P1.
- intros (Ant,(Suc,(HUP,(HA,HS)))).
  simpl.
  split.
  + intros HIn.
    contradict HUP.
    destruct (in_split _ _ HIn) as (A1,(A2,HAS)).
    rewrite HAS.
    LJm_reorder_antecedent (PPbot::A1++A2).
    apply LJm_exfalso2.
  + tauto.
- intros (Ant,(Suc,(HUP,(HA,HS)))).
  simpl.
  split.
  + tauto.
  + intros HInS HInA.
    contradict HUP.
    destruct (in_split _ _ HInA) as (A1,(A2,HAS)).
    destruct (in_split _ _ HInS) as (S1,(S2,HSS)).
    rewrite HAS,HSS.
    LJm_reorder_antecedent (PPatom n::A1++A2).
    LJm_reorder_succedent (PPatom n::S1++S2).
    apply LJm_axiom2.
- intros (Ant,(Suc,(HUP,(HA,HS)))).
  simpl.
  split.
  + intros HIn (Ant',(Suc',(HUP',(HA',HS')))).
    simpl.
    intros (L1,HAcc) H.
    destruct (HA' (PPimpl P1_1 P1_2)) as [H1|H1].
    {
      rewrite <-HAcc.
      rewrite in_app_iff.
      right.
      exact HIn.
    }
    * apply IHP1_1 in H.
      { contradict H. }
      exact H1.
    * apply IHP1_2.
      exact H1.
  + intros HIn H.
    destruct (LJm_saturate (P1_1::Ant) (P1_2::nil)) as (L1,(L2,HSat)).
    {
      intros HH.
      apply HUP.
      destruct (in_split _ _ HIn) as (S1,(S2,HSS)).
      rewrite HSS.
      LJm_reorder_succedent (PPimpl P1_1 P1_2::S1++S2).
      remember (S1++S2) as Suc'.
      clear HeqSuc'.
      induction Suc'.
      - apply LJm_impl_succedent.
        exact HH.
      - rewrite perm_swap.
        apply LJm_weak_succedent.
        exact IHSuc'.
    }
    apply (IHP1_2 (existT _ _ (exist _ _ HSat))).
    {
      simpl.
      rewrite in_app_iff.
      right.
      apply in_eq.
    }
    apply H.
    {
      simpl.
      exists (P1_1::L1).
      perm.
    }
    apply IHP1_1.
    simpl.
    rewrite in_app_iff.
    right.
    apply in_eq.
- intros (Ant,(Suc,(HUP,(HA,HS)))).
  simpl.
  split.
  + intros HIn.
    split.
    * apply IHP1_1.
      simpl.
      exact (proj1 (HA _ HIn)).
    * apply IHP1_2.
      exact (proj2 (HA _ HIn)).
  + intros HIn (H1,H2).
    destruct (HS _ HIn) as [HH|HH].
    * apply (IHP1_1 (existT _ _ (exist _ _ (conj HUP (conj HA HS))))).
      { exact HH. }
      exact H1.
    * apply (IHP1_2 (existT _ _ (exist _ _ (conj HUP (conj HA HS))))).
      { exact HH. }
      exact H2.
- intros (Ant,(Suc,(HUP,(HA,HS)))).
  simpl.
  split.
  + intros HIn.
    destruct (HA _ HIn) as [HH|HH].
    * left.
      apply IHP1_1.
      exact HH.
    * right.
      apply IHP1_2.
      exact HH.
  + intros HIn [H1|H2].
    * apply (fun x => proj2 (IHP1_1 _) x H1).
      simpl.
      exact (proj1 (HS _ HIn)).
    * apply (fun x => proj2 (IHP1_2 _) x H2).
      simpl.
      exact (proj2 (HS _ HIn)).
Qed.

Lemma LJm_KM_complete:
  forall L1 L2,
    (forall k:KripkeModel,
      forall(W:KF_worlds (KM_frame k)),
        (forall P, In P L1 -> KM_interp k W P) ->
        (exists P, In P L2 /\ KM_interp k W P)) ->
    LJm_provable L1 L2.
Proof.
intros L1 L2 HM.
destruct (LJm_dec L1 L2) as [HPr|HPrN].
{ exact HPr. }
exfalso.
destruct (LJm_saturate L1 L2 HPrN) as (L3,(L4,HSat)).
specialize (HM SaturatedUnprovableSequents
    (existT _ _ (exist _ _ HSat))).
destruct HM as (P,(HMA,HMB)).
- intros P HP.
  apply SUS_Lem.
  simpl.
  rewrite in_app_iff.
  right.
  exact HP.
- revert HMB.
  apply SUS_Lem.
  simpl.
  rewrite in_app_iff.
  right.
  exact HMA.
Qed.

Lemma LJ_KM_complete:
  forall P1 L1,
    (forall k:KripkeModel,
      forall(W:KF_worlds (KM_frame k)),
        (forall P, In P L1 -> KM_interp k W P) ->
        KM_interp k W P1) ->
    LJ_provable L1 P1.
Proof.
intros P1 L1 HM.
rewrite LJ_LJm_iff_single.
apply LJm_KM_complete.
intros k W H.
exists P1.
split.
{ apply in_eq. }
apply (HM k W H).
Qed.

Lemma LJ_KM_iff:
  forall L1 P1, LJ_provable L1 P1 <->
    forall k:KripkeModel,
      forall(W:KF_worlds (KM_frame k)),
        (forall P, In P L1 -> KM_interp k W P) ->
        KM_interp k W P1.
Proof.
intros L1 P1.
split.
- apply LJ_KM_sound.
- apply LJ_KM_complete.
Qed.

