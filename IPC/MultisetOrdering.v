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
    (LT2 <> nil) /\
    forall P1:A, In P1 LT1 ->
      exists P2:A, In P2 LT2 /\
        R P1 P2.

Global Instance multiset_ordering_comp:
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

Theorem multiset_ordering_wf: well_founded multiset_ordering.
Proof.
intros KL.
induction KL.
- exists.
  intros L (LH,(LT1,(LT2,((HL1,HL2),(HLI,HLA))))).
  apply Permutation_nil in HL2.
  apply app_eq_nil in HL2.
  destruct HL2 as (_,HL2).
  congruence.
- revert KL IHKL.
  induction a as (a,IHa) using (well_founded_ind R_wf).
  intros KL IHKL.
  remember IHKL as IHKL'; clear HeqIHKL'.
  induction IHKL as (KL,IHKL,IHIHKL).
  exists.
  intros L IHL.
  destruct (id IHL) as (LH,(LT1,(LT2,((HL1,HL2),(HLI,HLA))))).
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
      { exact HLI. }
      exact HLA.
    * apply IHKL.
      exists LH',LT1,LT2.
      {
        split.
        - split.
          + reflexivity.
          + exact HL2.
        - split.
          + exact HLI.
          + exact HLA.
      }
  + destruct (in_split _ _ Ha) as (LT2A,(LT2B,HLT2)).
    assert (HLT2' : Permutation LT2 (a :: LT2A ++ LT2B)) by (rewrite HLT2; perm).
    remember (LT2A ++ LT2B) as LT2'.
    clear LT2A LT2B Ha HLT2 HeqLT2'.
    rewrite HLT2' in HL2.
    clear HLI.
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

    assert (HLA3:
        exists LT1H LT1T,
          Permutation LT1 (LT1H++LT1T) /\
          (forall P1H, In P1H LT1H -> R P1H a) /\
          (forall P1, In P1 LT1T -> exists P2:A, In P2 LT2' /\ R P1 P2)).
    {
      clear HL1.
      induction LT1.
      - exists nil,nil.
        split.
        + reflexivity.
        + split.
          * intros P1H [].
          * intros P1 [].
      - destruct IHLT1 as (LT1H,(LT1T,(HLT1P,(HLT1H,HLT1T)))).
        {
          intros P1 HP1.
          apply HLA2.
          right.
          exact HP1.
        }
        destruct (HLA2 _ (in_eq _ _)) as (P2,([HP2A|HP2A],HP2B)).
        + exists (a0::LT1H),LT1T.
          split.
          {
            apply Permutation_cons.
            exact HLT1P.
          }
          split.
          * intros P1H [HP1H|HP1H].
            {
              rewrite <-HP1H.
              rewrite HP2A.
              exact HP2B.
            }
            apply HLT1H.
            exact HP1H.
          * exact HLT1T.
        + exists LT1H,(a0::LT1T).
          split.
          {
            rewrite HLT1P; perm.
          }
          split.
          * exact HLT1H.
          * intros P1 [HP1|HP1].
            {
              exists P2.
              split.
              - exact HP2A.
              - rewrite <-HP1.
                exact HP2B.
            }
            apply HLT1T.
            exact HP1.
    }
    clear HLA2.
    destruct HLA3 as (LT1H,(LT1T,(HLT1P,(HLT1H,HLT1T)))).
    rewrite HLT1P in HL1.
    setoid_replace (LH++LT1H++LT1T) with (LT1H++LH++LT1T)
        using relation (@Permutation A) in HL1; [|perm].
    clear LT1 HLT1P.
    clear IHL.
    revert L HL1.
    induction LT1H.
    * intros L HL1.
      assert (LT1T_nilselect: LT1T = nil \/ LT1T <> nil).
      {
        destruct LT1T.
        - left; reflexivity.
        - right; congruence.
      }
      destruct LT1T_nilselect as [LT1T_nil|LT1T_nonnil].
      {
        rewrite LT1T_nil in HL1.
        rewrite app_nil_r in HL1.
        rewrite app_nil_l in HL1.
        clear LT1T HLT1T LT1T_nil.
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
                + congruence.
                + intros P1 [].
            }
        }
      }
      assert (HMO: multiset_ordering L KL).
      {
        exists LH,LT1T,LT2'.
        split.
        - exact (conj HL1 HL2).
        - split.
          + destruct LT1T as [|LT1Th LT1T].
            * congruence.
            * destruct LT2' as [|LT2h' LT2']; [|congruence].
              destruct (HLT1T _ (in_eq _ _)) as (P2,([],_)).
          + intros P1 HP1.
            apply HLT1T.
            exact HP1.
      }
      clear HL1.
      revert L HMO.
      refine (match _ with Acc_intro x => x end).
      exact IHKL'.
    * intros L HL1.
      assert (Ha0in := in_eq a0 (LT1H++LH++LT1T)).
      rewrite <-HL1 in Ha0in.
      destruct (in_split _ _ Ha0in) as (LT1A,(LT1B,HLT1)).
      rewrite HLT1.
      rewrite HLT1 in HL1.
      clear L Ha0in HLT1.
      setoid_replace (LT1A++a0::LT1B) with (a0::LT1A++LT1B)
          using relation (@Permutation A) in HL1; [|perm].
      setoid_replace (LT1A++a0::LT1B) with (a0::LT1A++LT1B)
          using relation (@Permutation A); [|perm].
      apply Permutation_cons_inv in HL1.
      apply IHa.
      {
        apply HLT1H.
        apply in_eq.
      }
      apply IHLT1H.
      {
        intros P1H HP1H.
        apply HLT1H.
        right.
        exact HP1H.
      }
      exact HL1.
Qed.

End MultisetOrdering.
