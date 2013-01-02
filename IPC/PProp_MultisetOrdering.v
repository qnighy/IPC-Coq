Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Arith.Arith.
Require Import omega.Omega.
Require Import MyPermutations.
Require Import PProp.

Fixpoint DLI_prop_weight(p:PProp):nat :=
  match p with
  | PPbot => 1
  | PPatom _ => 1
  | PPimpl a b => 1 + DLI_prop_weight a + DLI_prop_weight b
  | PPconj a b => 2 + DLI_prop_weight a + DLI_prop_weight b
  | PPdisj a b => 1 + DLI_prop_weight a + DLI_prop_weight b
  end.

Lemma DLI_prop_weight_positive: forall P, DLI_prop_weight P > 0.
Proof.
intros [|n|a b|a b|a b].
- simpl; omega.
- simpl; omega.
- simpl; omega.
- simpl; omega.
- simpl; omega.
Qed.

Fixpoint DLI_multiset_max(L:list PProp):nat :=
  match L with
  | nil => 0
  | P :: L' => max (DLI_prop_weight P) (DLI_multiset_max L')
  end.

Instance DLI_multiset_max_compat:
  Proper (@Permutation PProp ==> eq)
    DLI_multiset_max.
Proof.
unfold Proper,respectful.
intros LA LB HL.
induction HL.
- reflexivity.
- simpl.
  rewrite IHHL.
  reflexivity.
- simpl.
  rewrite Max.max_assoc.
  rewrite Max.max_assoc.
  rewrite (Max.max_comm (DLI_prop_weight y)).
  reflexivity.
- congruence.
Qed.

Lemma DLI_multiset_max_app:
  forall L1 L2, DLI_multiset_max (L1++L2) =
    max (DLI_multiset_max L1) (DLI_multiset_max L2).
Proof.
intros L1 L2.
induction L1.
- rewrite Max.max_0_l.
  reflexivity.
- simpl.
  rewrite IHL1.
  apply Max.max_assoc.
Qed.

Lemma DLI_multiset_max_le:
  forall P L, In P L -> DLI_prop_weight P <= DLI_multiset_max L.
Proof.
intros P L HP.
induction L.
- contradict HP.
- destruct HP as [HP|HP].
  + apply le_trans with (DLI_prop_weight a).
    * rewrite HP.
      apply le_refl.
    * apply Max.le_max_l.
  + apply le_trans with (DLI_multiset_max L).
    * apply IHL,HP.
    * apply Max.le_max_r.
Qed.

Lemma DLI_multiset_max_nil_or_exists:
  forall L, L = nil \/ exists P, In P L /\ DLI_multiset_max L = DLI_prop_weight P.
Proof.
intros L.
induction L.
- left.
  reflexivity.
- right.
  destruct IHL as [IHL|(P,(HPA,HPB))].
  + rewrite IHL.
    exists a.
    split.
    * left.
      reflexivity.
    * apply Max.max_0_r.
  + simpl.
    destruct (Max.max_dec (DLI_prop_weight a) (DLI_multiset_max L)) as [HM|HM].
    * rewrite HM.
      exists a.
      split.
      { left; reflexivity. }
      reflexivity.
    * rewrite HM.
      exists P.
      split.
      { right; exact HPA. }
      exact HPB.
Qed.

Definition DLI_multiset_ordering(L1 L2:list PProp):Prop :=
  exists LH LT1 LT2,
    (Permutation L1 (LH ++ LT1) /\
     Permutation L2 (LH ++ LT2)) /\
    exists P2:PProp, In P2 LT2 /\ forall P1:PProp, In P1 LT1 ->
      DLI_prop_weight P1 < DLI_prop_weight P2.

Instance DLI_multiset_ordering_compat:
  Proper (@Permutation PProp ==> @Permutation PProp ==> iff)
    DLI_multiset_ordering.
Proof.
unfold Proper,respectful.
intros L1A L1B H1 L2A L2B H2.
split.
- intros (LH,(LT1,(LT2,((HL1,HL2),H)))).
  exists LH,LT1,LT2.
  split.
  + split.
    * rewrite <-H1; exact HL1.
    * rewrite <-H2; exact HL2.
  + exact H.
- intros (LH,(LT1,(LT2,((HL1,HL2),H)))).
  exists LH,LT1,LT2.
  split.
  + split.
    * rewrite H1; exact HL1.
    * rewrite H2; exact HL2.
  + exact H.
Qed.

Lemma DLI_multiset_ordering_cons_inv:
  forall P L1 L2,
    DLI_multiset_ordering (P::L1) (P::L2) ->
      DLI_multiset_ordering L1 L2.
Proof.
intros P L1 L2 (LH,(LT1,(LT2,((HL1,HL2),(P2,(HP2,HL)))))).
destruct (in_dec PProp_dec P LH) as [HPin|HPin].
- destruct (in_split _ _ HPin) as (LHA,(LHB,HLH)).
  exists (LHA++LHB), LT1, LT2.
  split.
  + split.
    * apply Permutation_cons_inv with (a:=P).
      rewrite HL1.
      rewrite HLH.
      perm.
    * apply Permutation_cons_inv with (a:=P).
      rewrite HL2.
      rewrite HLH.
      perm.
  + exists P2.
    split.
    * exact HP2.
    * exact HL.
- assert (HPL1 := in_eq P L1).
  rewrite HL1 in HPL1.
  rewrite in_app_iff in HPL1.
  destruct HPL1 as [HPL1|HPL1].
  { contradiction. }
  assert (HPL2 := in_eq P L2).
  rewrite HL2 in HPL2.
  rewrite in_app_iff in HPL2.
  destruct HPL2 as [HPL2|HPL2].
  { contradiction. }
  destruct (in_split _ _ HPL1) as (LT1A,(LT1B,HLT1)).
  destruct (in_split _ _ HPL2) as (LT2A,(LT2B,HLT2)).
  exists LH,(LT1A++LT1B),(LT2A++LT2B).
  split.
  + split.
    * apply Permutation_cons_inv with (a:=P).
      rewrite HL1.
      rewrite HLT1.
      perm.
    * apply Permutation_cons_inv with (a:=P).
      rewrite HL2.
      rewrite HLT2.
      perm.
  + destruct (PProp_dec P2 P) as [HPeq|HPneq].
    * exfalso.
      specialize (HL _ HPL1).
      rewrite <-HPeq in HL.
      omega.
    * exists P2.
      split.
      {
        rewrite in_app_iff.
        rewrite HLT2 in HP2.
        rewrite in_app_iff in HP2.
        destruct HP2 as [HP2|[HP2|HP2]].
        - left.
          exact HP2.
        - congruence.
        - right.
          exact HP2.
      }
      {
        intros P1 HP1.
        apply HL.
        rewrite HLT1.
        rewrite in_app_iff in HP1.
        rewrite in_app_iff.
        destruct HP1 as [HP1|HP1].
        - left.
          exact HP1.
        - right.
          right.
          exact HP1.
      }
Qed.

Lemma DLI_multiset_ordering_max_le:
  forall L1 L2,
    DLI_multiset_ordering L1 L2 ->
      DLI_multiset_max L1 <= DLI_multiset_max L2.
Proof.
intros L1 L2 (LH,(LT1,(LT2,((HL1,HL2),(P2,(HP2,HL)))))).
destruct (DLI_multiset_max_nil_or_exists L1) as [HL1M|(P,(HPA,HPB))].
{
  rewrite HL1M.
  apply le_0_n.
}
rewrite HPB.
rewrite HL1 in HPA.
rewrite in_app_iff in HPA.
destruct HPA as [HPA|HPA].
- apply DLI_multiset_max_le.
  rewrite HL2.
  rewrite in_app_iff.
  left.
  exact HPA.
- apply le_trans with (DLI_prop_weight P2).
  + apply lt_le_weak.
    apply HL.
    exact HPA.
  + apply DLI_multiset_max_le.
    rewrite HL2.
    rewrite in_app_iff.
    right.
    exact HP2.
Qed.

Lemma DLI_multiset_ordering_irrefl: forall L, ~DLI_multiset_ordering L L.
Proof.
intros L H.
induction L.
- destruct H as (LH,(LT1,(LT2,((HL1,HL2),(P2,(HP2,HL)))))).
  apply Permutation_nil in HL2.
  apply app_eq_nil in HL2.
  destruct HL2 as (HL2A,HL2B).
  rewrite HL2B in HP2.
  contradict HP2.
- apply DLI_multiset_ordering_cons_inv in H.
  apply IHL,H.
Qed.

Lemma DLI_multiset_ordering_wellfounded: well_founded DLI_multiset_ordering.
Proof.

Qed.

Lemma DLI_multiset_ordering_wellfounded: well_founded DLI_multiset_ordering.
Proof.
intros KL.
induction KL as (KL,IH_mw) using (well_founded_ind (well_founded_ltof _ DLI_multiset_max)).
unfold ltof in IH_mw.
remember (DLI_multiset_max KL) as n.
symmetry in Heqn.
apply NPeano.Nat.eq_le_incl in Heqn.

rewrite <-(app_nil_l KL).
remember (@nil PProp) as KT.
assert (KTle: forall P:PProp, In P KT -> DLI_multiset_max KL <= DLI_prop_weight P).
{ rewrite HeqKT; intros P []. }
clear HeqKT.
revert KT KTle.

induction KL as (KL,IH_ll) using (well_founded_ind (well_founded_ltof _ (@length PProp))).
unfold ltof in IH_ll.
intros KT KTle.
exists.
intros L HL.
assert (HMW := DLI_multiset_ordering_max_le _ _ HL).
apply le_lt_or_eq in HMW.
destruct HMW as [HMW|HMW].
- apply IH_mw with (KT:=nil).
  + apply lt_le_trans with (DLI_multiset_max (KT++KL)).
    * exact HMW.
    * exact Heqn.
- apply IH_ll.
  + 


intros KL.
induction KL as (KL,IH_mw) using (well_founded_ind (well_founded_ltof _ DLI_multiset_max)).
unfold ltof in IH_mw.
remember (DLI_multiset_max KL) as n.
symmetry in Heqn.
apply NPeano.Nat.eq_le_incl in Heqn.
exists.
intros L HL.
induction L as (L,IH_ll) using (well_founded_ind (well_founded_ltof _ (@length PProp))).
unfold ltof in IH_ll.
assert (HMW := DLI_multiset_ordering_max_le _ _ HL).
apply le_lt_or_eq in HMW.
destruct HMW as [HMW|HMW].
- apply IH_mw.
  apply lt_le_trans with (DLI_multiset_max KL).
  + exact HMW.
  + exact Heqn.
- apply IH_ll.
  + 





intros KL.
induction KL as (KL,IH_mw) using (well_founded_ind (well_founded_ltof _ DLI_multiset_max)).
unfold ltof in IH_mw.
remember (DLI_multiset_max KL) as n.
symmetry in Heqn.
apply NPeano.Nat.eq_le_incl in Heqn.
induction KL as (KL,IH_ll) using (well_founded_ind (well_founded_ltof _ (@length PProp))).
unfold ltof in IH_ll.
exists.
intros L HL.
assert (HMW := DLI_multiset_ordering_max_le _ _ HL).
apply le_lt_or_eq in HMW.
destruct HMW as [HMW|HMW].
- apply IH_mw.
  apply lt_le_trans with (DLI_multiset_max KL).
  + exact HMW.
  + exact Heqn.
- apply IH_ll.
  + 

intros L (LH,(LT1,(LT2,((HL1,HL2),(P2,(HP2,HL)))))).
intros L HL.
remember (DLI_multiset_max


- intros KL Heqn.
  exists.
  intros L (LH,(LT1,(LT2,((HL1,HL2),(P2,(HP2,HL)))))).
  exfalso.
  assert (HIneq1: DLI_prop_weight P2 > 0).
  {
    apply DLI_prop_weight_positive.
  }
  assert (HIneq2: DLI_prop_weight P2 <= 0).
  {
    rewrite Heqn.
    apply DLI_multiset_max_le.
    rewrite HL2.
    rewrite in_app_iff.
    right.
    exact HP2.
  }
  omega.
- 
Qed.

