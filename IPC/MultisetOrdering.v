Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Arith.Arith.
Require Import omega.Omega.
Require Import MyPermutations.

Section MultisetOrdering.

Hypothesis A:Type.
Hypothesis R: relation A.
Hypothesis R_wf: well_founded R.

Definition multiset_ordering(L1 L2:list A):Prop :=
  exists LH LT1 LT2,
    (Permutation L1 (LH ++ LT1) /\
     Permutation L2 (LH ++ LT2)) /\
    (exists PI:A, In PI LT2) /\
    forall P1:A, In P1 LT1 ->
      exists P2:A, In P2 LT2 /\
        R P1 P2.

Instance multiset_ordering_comp:
  Proper (@Permutation A ==> @Permutation A ==> iff)
    multiset_ordering.
Proof.
unfold Proper, respectful.
intros L1A L1B H1 L2A L2B H2.
split.
- intros (LH,(LT1,(LT2,((HL1,HL2),H)))).
  exists LH,LT1,LT2.
  split.
  + rewrite <-H1.
    rewrite <-H2.
    exact (conj HL1 HL2).
  + exact H.
- intros (LH,(LT1,(LT2,((HL1,HL2),H)))).
  exists LH,LT1,LT2.
  split.
  + rewrite H1.
    rewrite H2.
    exact (conj HL1 HL2).
  + exact H.
Qed.

Instance multiset_ordering_Acc_comp:
  Proper (@Permutation A ==> iff)
    (Acc multiset_ordering).
Proof.
unfold Proper, respectful.
intros LA LB Heq.
split.
- intros H.
  induction H.
  exists.
  intros y Hy.
  apply H.
  rewrite Heq.
  exact Hy.
- intros H.
  induction H.
  exists.
  intros y Hy.
  apply H.
  rewrite <-Heq.
  exact Hy.
Qed.

Lemma maximal_exists_cont:
  forall PP:Prop,
    forall L,
      (
        L = nil \/
        (exists a, In a L /\ forall b, In b L -> clos_trans _ R a b -> PP)
      -> PP) -> PP.
Proof.
intros PP L.
induction L.
- intros H.
  apply H.
  left.
  reflexivity.
- intros H.
  apply IHL.
  clear IHL.
  intros IHL'.
  revert H.
  destruct IHL' as [IHL'|(b,(HbA,HbB))].
  + rewrite IHL'.
    intros H.
    apply H.
    right.
    exists a.
    split.
    * apply in_eq.
    * intros c [Hc|[]] HR.
      rewrite Hc in HR; clear Hc.
      induction c using (well_founded_induction (wf_clos_trans _ _ R_wf)).
      apply (H0 c); exact HR.
  + assert (HabS: ((clos_trans A R a b \/ (clos_trans A R a b -> PP))->PP)->PP).
    {
      intros H.
      apply H.
      right.
      intros HH.
      apply H.
      left.
      exact HH.
    }
    intros H.
    apply HabS.
    intros HabS'.
    clear HabS.
    revert H.
    assert (HbaS: ((clos_trans A R b a \/ (clos_trans A R b a -> PP))->PP)->PP).
    {
      intros H.
      apply H.
      right.
      intros HH.
      apply H.
      left.
      exact HH.
    }
    intros H.
    apply HbaS.
    intros HbaS'.
    clear HbaS.
    revert H.
    destruct HbaS' as [HbaS|HbaS]; [destruct HabS' as [HabS|HabS]|].
    * exfalso.
      assert (HaS := t_trans _ _ _ _ _ HabS HbaS).
      clear HabS HbaS.
      induction a using (well_founded_ind (wf_clos_trans _ _ R_wf)).
      apply (H a); exact HaS.
    * intros H.
      apply H.
      clear H.
      right.
      exists a.
      split.
      { left; reflexivity. }
      intros c [Hc|Hc].
      {
        rewrite Hc; clear Hc.
        induction c using (well_founded_ind (wf_clos_trans _ _ R_wf)).
        intros HH.
        apply (H c); exact HH.
      }
      intros H.
      apply (HbB c Hc).
      apply t_trans with (y:=a); trivial.
    * intros H.
      apply H.
      clear H.
      right.
      exists b.
      split.
      { right; exact HbA. }
      intros c [Hc|Hc].
      { rewrite <-Hc; exact HbaS. }
      apply HbB,Hc.
Qed.

Theorem multiset_ordering_wf: well_founded multiset_ordering.
Proof.
intros KL.
remember (length KL) as n.
revert KL Heqn.
induction n.
- admit.
- intros KL' Heqn.
  apply maximal_exists_cont with (L:=KL').
  intros [IHKL|(a,(HaKL,Ha_max'))].
  { rewrite IHKL in Heqn; simpl in Heqn; congruence. }
  destruct (in_split _ _ HaKL) as (KL1,(KL2,HKLS)).
  assert (HKLS' : Permutation KL' (a::KL1++KL2)) by (rewrite HKLS; perm).
  clear HKLS.
  rewrite HKLS' in Heqn |- *.
  simpl in Heqn; apply eq_add_S in Heqn.
  assert (Ha_max:
      forall b, In b (a::KL1++KL2) -> clos_trans A R a b ->
        Acc multiset_ordering (a::KL1++KL2)).
  {
    intros b.
    rewrite <-HKLS'.
    apply Ha_max'.
  }
  clear Ha_max'.
  remember (KL1 ++ KL2) as KL.
  clear KL' KL1 KL2 HaKL HKLS' HeqKL.
  assert (IHKL := IHn _ Heqn).
  clear n IHn Heqn.

  revert KL Ha_max IHKL.
  induction a as (a,IHa) using (well_founded_ind R_wf).
  intros KL Ha_max IHKL.
  remember IHKL as IHKL'; clear HeqIHKL'.
  induction IHKL as (KL,IHKL,IHIHKL).
  exists.
  intros L IHL.
  destruct (id IHL) as (LH,(LT1,(LT2,((HL1,HL2),((PI,HPI),HLA))))).
  assert (Ha := in_eq a KL).
  rewrite HL2 in Ha.
  rewrite in_app_iff in Ha.
  destruct Ha as [Ha|Ha].
  + destruct (in_split _ _ Ha) as (LH1,(LH2,HLH)).
    rewrite HLH in HL1, HL2.
    clear LH Ha HLH.
    setoid_replace ((LH1 ++ a :: LH2) ++ LT2)
        with       (a :: (LH1 ++ LH2) ++ LT2)
        using relation (@Permutation A) in HL2; [|perm].
    apply Permutation_cons_inv in HL2.
    setoid_replace ((LH1 ++ a :: LH2) ++ LT1)
        with       (a :: (LH1 ++ LH2) ++ LT1)
        using relation (@Permutation A) in HL1; [|perm].
    remember (LH1 ++ LH2) as LH'; clear LH1 LH2 HeqLH'.
    rewrite HL1.
    apply IHIHKL.
    * rewrite HL2.
      exists LH',LT1,LT2.
      split.
      { split; reflexivity. }
      split.
      { exists PI; exact HPI. }
      exact HLA.
    * {
        intros b Hb Hab.
        simpl in Hb.
        rewrite in_app_iff in Hb.
        rewrite <-or_assoc in Hb.
        destruct Hb as [Hb|Hb].
        - rewrite <-HL1.
          apply (or_introl (B:=In b LT2)) in Hb.
          rewrite or_assoc in Hb.
          rewrite <-in_app_iff in Hb.
          rewrite <-HL2 in Hb.
          clear LT1 LT2 LH' HL1 HL2 PI HPI HLA.
          revert L IHL.
          refine (match _ with Acc_intro x => x end).
          apply Ha_max with (b:=b).
          + exact Hb.
          + exact Hab.
        - destruct (HLA _ Hb) as (P2,(HP2A,HP2B)).
          rewrite <-HL1.
          assert (HP2A': In P2 (a :: KL)).
          {
            right.
            rewrite HL2.
            rewrite in_app_iff.
            right.
            exact HP2A.
          }
          clear LT1 LT2 LH' HL1 HL2 PI HPI HLA Hb HP2A.
          revert L IHL.
          refine (match _ with Acc_intro x => x end).
          apply Ha_max with (b:=P2).
          + exact HP2A'.
          + apply t_trans with b.
            * exact Hab.
            * apply t_step.
              exact HP2B.
      }
    * apply IHKL.
      exists LH',LT1,LT2.
      {
        split.
        - split.
          + reflexivity.
          + exact HL2.
        - split.
          + exists PI.
            exact HPI.
          + exact HLA.
      }
  + destruct (in_split _ _ Ha) as (LT2A,(LT2B,HLT2)).
    assert (HLT2' : Permutation LT2 (a :: LT2A ++ LT2B)) by (rewrite HLT2; perm).
    remember (LT2A ++ LT2B) as LT2'.
    clear LT2A LT2B Ha HLT2 HeqLT2'.
    rewrite HLT2' in HL2,HPI.
    assert (HLA2:
        forall P1:A, In P1 LT1 -> exists P2:A, In P2 (a::LT2') /\ R P1 P2).
    {
      intros P1 HP1.
      specialize (HLA P1 HP1).
      destruct HLA as (P2,(HP2A,HP2B)).
      exists P2.
      split; [|exact HP2B].
      rewrite <-HLT2'.
      exact HP2A.
    }
    clear LT2 HLT2' HLA.
    setoid_replace (LH ++ a :: LT2')
        with       (a :: LH ++ LT2')
        using relation (@Permutation A) in HL2; [|perm].
    apply Permutation_cons_inv in HL2.
    clear PI HPI.
    assert (HLA3:
        LT1 = nil \/
          (LT1 <> nil /\ exists P1, In P1 LT1 /\ R P1 a) \/
          (LT1 <> nil /\ forall P1, In P1 LT1 -> exists P2:A, In P2 LT2' /\ R P1 P2)).
    {
      clear HL1.
      induction LT1.
      - left.
        reflexivity.
      - right.
        destruct IHLT1 as [IHLT1|[IHLT1|IHLT1]].
        + intros P1 HP1.
          apply HLA2.
          right.
          exact HP1.
        + specialize (HLA2 _ (in_eq _ _)).
          destruct HLA2 as (P2,([HP2A|HP2A],HP2B)).
          * rewrite HP2A.
            left.
            split.
            { congruence. }
            exists a0.
            split.
            { apply in_eq. }
            exact HP2B.
          * rewrite IHLT1.
            right.
            split.
            { congruence. }
            intros P1 [HP1|[]].
            exists P2.
            split.
            { exact HP2A. }
            rewrite <-HP1.
            exact HP2B.
        + left.
          destruct IHLT1 as (_,(P1,(HP1A,HP1B))).
          split.
          { congruence. }
          exists P1.
          split.
          * right.
            exact HP1A.
          * exact HP1B.
        + specialize (HLA2 _ (in_eq _ _)).
          destruct HLA2 as (P2,([HP2A|HP2A],HP2B)).
          * left.
            split.
            { congruence. }
            exists a0.
            split.
            { apply in_eq. }
            rewrite HP2A.
            exact HP2B.
          * right.
            split.
            { congruence. }
            intros P1 [HP1|HP1].
            {
              exists P2.
              split.
              - exact HP2A.
              - rewrite <-HP1.
                exact HP2B.
            }
            exact ((proj2 IHLT1) P1 HP1).
    }
    clear HLA2.
    destruct HLA3 as [HLA3|[HLA3|HLA3]].
    * rewrite HLA3 in HL1.
      clear LT1 HLA3.
      rewrite app_nil_r in HL1.
      rewrite <-HL1 in HL2.
      clear LH HL1.
      {
        destruct LT2'.
        - rewrite app_nil_r in HL2.
          rewrite <-HL2.
          exact IHKL'.
        - apply IHKL.
          exists L,nil,(a0::LT2').
          {
            split.
            - split.
              + rewrite app_nil_r.
                reflexivity.
              + exact HL2.
            - split.
              + exists a0.
                apply in_eq.
              + intros P1 [].
          }
      }
    * 
    * assert (HMO: multiset_ordering L KL).
      {
        exists LH,LT1,LT2'.
        split.
        - exact (conj HL1 HL2).
        - split.
          + destruct LT1 as [|LT1h LT1].
            * destruct HLA3; congruence.
            * destruct HLA3 as (_,HLA3).
              specialize (HLA3 _ (in_eq _ _)).
              destruct HLA3 as (P2,(HP2A,HP2B)).
              exists P2.
              exact HP2A.
          + exact (proj2 HLA3).
      }
      clear IHL HL1.
      revert L HMO.
      refine (match _ with Acc_intro x => x end).
      exact IHKL'.
Qed.

End MultisetOrdering.
