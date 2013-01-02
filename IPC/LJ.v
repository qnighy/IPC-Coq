Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.

Inductive PProp:Set :=
  | PPbot : PProp
  | PPatom : nat -> PProp
  | PPimpl : PProp -> PProp -> PProp
  | PPconj : PProp -> PProp -> PProp
  | PPdisj : PProp -> PProp -> PProp.

Lemma PProp_dec : forall p1 p2:PProp, {p1=p2} + {p1<>p2}.
Proof.
decide equality.
apply eq_nat_dec.
Qed.

Instance In_compat_perm_PProp:
    Proper (eq ==> @Permutation PProp ==> iff) (@In PProp).
Proof.
apply In_compat_perm.
apply PProp_dec.
Qed.

Definition PProp_small(a b:PProp):Prop :=
  ((exists x, b = PPimpl a x) \/ (exists x, b = PPimpl x a)) \/
  ((exists x, b = PPconj a x) \/ (exists x, b = PPconj x a)) \/
  ((exists x, b = PPdisj a x) \/ (exists x, b = PPdisj x a)).

Lemma PProp_small_wellfounded: well_founded PProp_small.
Proof.
intros p.
induction p.
- exists.
  intros y Hy.
  destruct Hy as [[Hy|Hy]|[[Hy|Hy]|[Hy|Hy]]];
    destruct Hy as (z,Hz);
    congruence.
- exists.
  intros y Hy.
  destruct Hy as [[Hy|Hy]|[[Hy|Hy]|[Hy|Hy]]];
    destruct Hy as (z,Hz);
    congruence.
- exists.
  intros y Hy.
  destruct Hy as [[Hy|Hy]|[[Hy|Hy]|[Hy|Hy]]];
    destruct Hy as (z,Hz);
    congruence.
- exists.
  intros y Hy.
  destruct Hy as [[Hy|Hy]|[[Hy|Hy]|[Hy|Hy]]];
    destruct Hy as (z,Hz);
    congruence.
- exists.
  intros y Hy.
  destruct Hy as [[Hy|Hy]|[[Hy|Hy]|[Hy|Hy]]];
    destruct Hy as (z,Hz);
    congruence.
Qed.

Inductive LJ_provable : list PProp -> PProp -> Prop :=
  | LJ_perm P1 L1 L2 :
      Permutation L1 L2 ->
      LJ_provable L1 P1 ->
      LJ_provable L2 P1
  | LJ_weak P1 P2 L1 :
      LJ_provable L1 P2 ->
      LJ_provable (P1::L1) P2
  | LJ_contr P1 P2 L1 :
      LJ_provable (P1::P1::L1) P2 ->
      LJ_provable (P1::L1) P2
  | LJ_axiom P1 :
      LJ_provable (P1::nil) P1
  | LJ_exfalso P1 :
      LJ_provable (PPbot::nil) P1
  | LJ_impl_antecedent P1 P2 P3 L1 :
      LJ_provable (L1) P1 ->
      LJ_provable (P2::L1) P3 ->
      LJ_provable (PPimpl P1 P2::L1) P3
  | LJ_impl_succedent P1 P2 L1 :
      LJ_provable (P1::L1) P2 ->
      LJ_provable L1 (PPimpl P1 P2)
  | LJ_conj_antecedent P1 P2 P3 L1 :
      LJ_provable (P1::P2::L1) P3 ->
      LJ_provable (PPconj P1 P2::L1) P3
  | LJ_conj_succedent P1 P2 L1 :
      LJ_provable L1 P1 ->
      LJ_provable L1 P2 ->
      LJ_provable L1 (PPconj P1 P2)
  | LJ_disj_antecedent P1 P2 P3 L1 :
      LJ_provable (P1::L1) P3 ->
      LJ_provable (P2::L1) P3 ->
      LJ_provable (PPdisj P1 P2::L1) P3
  | LJ_disj_succedent_l P1 P2 L1 :
      LJ_provable L1 P1 ->
      LJ_provable L1 (PPdisj P1 P2)
  | LJ_disj_succedent_r P1 P2 L1 :
      LJ_provable L1 P2 ->
      LJ_provable L1 (PPdisj P1 P2).

Ltac LJ_reorder_antecedent L :=
  apply (LJ_perm _ L); [perm|].

Instance LJ_provable_compat : Proper (@Permutation _==>eq==>iff) LJ_provable.
Proof.
unfold Proper,respectful.
intros L1 L2 HL P1 P2 HP.
split.
- intros H.
  rewrite <-HP.
  exact (LJ_perm P1 L1 L2 HL H).
- intros H.
  rewrite ->HP.
  exact (LJ_perm P2 L2 L1 (Permutation_sym HL) H).
Qed.

Lemma LJ_weakN: forall P1 L1 L2, LJ_provable L1 P1 -> LJ_provable (L2++L1) P1.
Proof.
intros P1 L1 L2 H.
induction L2.
- exact H.
- apply LJ_weak,IHL2.
Qed.

Lemma LJ_contrN: forall P1 L1 L2, LJ_provable (L2++L2++L1) P1 -> LJ_provable (L2++L1) P1.
Proof.
intros P1 L1 L2 H.
revert L1 H.
induction L2.
- intros L1 H.
  exact H.
- intros L1 H.
  LJ_reorder_antecedent (L2++(a::L1)).
  apply IHL2.
  LJ_reorder_antecedent (a::L2++L2++L1).
  apply LJ_contr.
  LJ_reorder_antecedent ((a::L2)++(a::L2)++L1).
  exact H.
Qed.

Lemma LJ_bot_elim: forall P1 L1, LJ_provable L1 PPbot -> LJ_provable L1 P1.
Proof.
intros P1 L1 H.
remember PPbot as P2 in H.
induction H.
- rewrite <-H.
  apply IHLJ_provable,HeqP2.
- apply LJ_weak,IHLJ_provable,HeqP2.
- apply LJ_contr,IHLJ_provable,HeqP2.
- rewrite HeqP2.
  apply LJ_exfalso.
- apply LJ_exfalso.
- apply LJ_impl_antecedent.
  + apply H.
  + apply IHLJ_provable2,HeqP2.
- congruence.
- apply LJ_conj_antecedent,IHLJ_provable,HeqP2.
- congruence.
- apply LJ_disj_antecedent.
  + apply IHLJ_provable1,HeqP2.
  + apply IHLJ_provable2,HeqP2.
- congruence.
- congruence.
Qed.

Lemma LJ_conj_elim_l:
  forall P1 P2 L1,
    LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P1.
Proof.
intros P1 P2 L1 H.
remember (PPconj P1 P2) as P3 in H.
induction H.
- rewrite <-H.
  apply IHLJ_provable,HeqP3.
- apply LJ_weak,IHLJ_provable,HeqP3.
- apply LJ_contr,IHLJ_provable,HeqP3.
- rewrite HeqP3.
  apply LJ_conj_antecedent.
  LJ_reorder_antecedent (P2::P1::nil).
  apply LJ_weak.
  apply LJ_axiom.
- apply LJ_exfalso.
- apply LJ_impl_antecedent.
  + apply H.
  + apply IHLJ_provable2,HeqP3.
- congruence.
- apply LJ_conj_antecedent,IHLJ_provable,HeqP3.
- congruence.
- apply LJ_disj_antecedent.
  + apply IHLJ_provable1,HeqP3.
  + apply IHLJ_provable2,HeqP3.
- congruence.
- congruence.
Qed.

Lemma LJ_conj_elim_r:
  forall P1 P2 L1,
    LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P2.
Proof.
intros P1 P2 L1 H.
remember (PPconj P1 P2) as P3 in H.
induction H.
- rewrite <-H.
  apply IHLJ_provable,HeqP3.
- apply LJ_weak,IHLJ_provable,HeqP3.
- apply LJ_contr,IHLJ_provable,HeqP3.
- rewrite HeqP3.
  apply LJ_conj_antecedent.
  apply LJ_weak.
  apply LJ_axiom.
- apply LJ_exfalso.
- apply LJ_impl_antecedent.
  + apply H.
  + apply IHLJ_provable2,HeqP3.
- congruence.
- apply LJ_conj_antecedent,IHLJ_provable,HeqP3.
- congruence.
- apply LJ_disj_antecedent.
  + apply IHLJ_provable1,HeqP3.
  + apply IHLJ_provable2,HeqP3.
- congruence.
- congruence.
Qed.

Lemma LJ_impl_elim:
  forall P1 P2 L1,
    LJ_provable L1 (PPimpl P1 P2) -> LJ_provable (P1::L1) P2.
Proof.
intros P1 P2 L1 H.
remember (PPimpl P1 P2) as P3 in H.
induction H.
- rewrite <-H.
  apply IHLJ_provable,HeqP3.
- LJ_reorder_antecedent (P0::P1::L1).
  apply LJ_weak,IHLJ_provable,HeqP3.
- LJ_reorder_antecedent (P0::P1::L1).
  apply LJ_contr.
  LJ_reorder_antecedent (P1::P0::P0::L1).
  apply IHLJ_provable,HeqP3.
- rewrite HeqP3.
  LJ_reorder_antecedent (PPimpl P1 P2::P1::nil).
  apply LJ_impl_antecedent.
  + apply LJ_axiom.
  + LJ_reorder_antecedent (P1::P2::nil).
    apply LJ_weak,LJ_axiom.
- apply LJ_weak,LJ_exfalso.
- LJ_reorder_antecedent (PPimpl P0 P3::P1::L1).
  apply LJ_impl_antecedent.
  + apply LJ_weak,H.
  + LJ_reorder_antecedent (P1::P3::L1).
    apply IHLJ_provable2,HeqP3.
- congruence.
- LJ_reorder_antecedent (PPconj P0 P3::P1::L1).
  apply LJ_conj_antecedent.
  LJ_reorder_antecedent (P1::P0::P3::L1).
  apply IHLJ_provable,HeqP3.
- congruence.
- LJ_reorder_antecedent (PPdisj P0 P3::P1::L1).
  apply LJ_disj_antecedent.
  + LJ_reorder_antecedent (P1::P0::L1).
    apply IHLJ_provable1,HeqP3.
  + LJ_reorder_antecedent (P1::P3::L1).
    apply IHLJ_provable2,HeqP3.
- congruence.
- congruence.
Qed.

Fixpoint replicate{A:Type} (n:nat) (a:A):list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Lemma In_replicate_eq: forall{A:Type} (a b:A) (n:nat), In a (replicate n b) -> a = b.
Proof.
intros A a b n.
induction n.
- intros [].
- intros [H|H].
  + congruence.
  + apply IHn,H.
Qed.

Lemma eq_then_Permutation: forall{A:Type} (l1 l2:list A), l1 = l2 -> Permutation l1 l2.
Proof.
intros A l1 l2 H.
rewrite H; reflexivity.
Qed.

Lemma LJ_cut_permselect:
  forall(P1 P2:PProp) (L1 L2:list PProp) (n:nat),
    Permutation (P1::L1) (replicate n P2++L2) ->
      (
        P1 = P2 /\ match n with
        | O => False
        | S n' => Permutation L1 (replicate n' P2++L2)
        end
      ) \/ (
        exists L2',
          Permutation L2 (P1::L2') /\
          Permutation L1 (replicate n P2++L2')
      ).
Proof.
intros P1 P2 L1 L2 n HP.
assert (HI:=in_eq P1 L1).
rewrite HP in HI.
rewrite in_app_iff in HI.
destruct HI as [HI|HI].
- left.
  split.
  + apply In_replicate_eq in HI.
    exact HI.
  + destruct n as [|n].
    * contradict HI.
    * apply In_replicate_eq in HI.
      rewrite HI in HP.
      apply Permutation_cons_inv with (a:=P2).
      exact HP.
- right.
  destruct (in_split _ _ HI) as (L2A,(L2B,HL2)).
  exists (L2A++L2B).
  split.
  + rewrite HL2.
    perm.
  + apply Permutation_cons_inv with (a:=P1).
    rewrite HP.
    rewrite HL2.
    perm.
Qed.

Lemma LJ_cut_permselect_nil:
  forall(P1 P2:PProp) (L2:list PProp) (n:nat),
    Permutation (P1::nil) (replicate n P2++L2) ->
      (
        P1 = P2 /\ n = 1 /\ L2 = nil
      ) \/ (
        n = 0 /\ L2 = (P1::nil)
      ).
intros P1 P2 L2 n HP.
apply Permutation_length_1_inv in HP.
destruct n as [|n].
- right.
  split.
  + reflexivity.
  + exact HP.
- left.
  change (P2::(replicate n P2++L2) = P1::nil) in HP.
  split.
  {
    congruence.
  }
  assert (HP2: replicate n P2++L2 = nil) by congruence.
  destruct n as [|n]; simpl in HP2; [|congruence].
  split.
  + reflexivity.
  + exact HP2.
Qed.

Lemma LJ_disj_elim2_withcut:
  forall P1 P2 P3 L1 L2,
    (forall PA LA1 LA2,
      LJ_provable LA1 P1 -> LJ_provable (P1::LA2) PA -> LJ_provable (LA1++LA2) PA) ->
    (forall PA LA1 LA2,
      LJ_provable LA1 P2 -> LJ_provable (P2::LA2) PA -> LJ_provable (LA1++LA2) PA) ->
    LJ_provable L1 (PPdisj P1 P2) ->
    LJ_provable (P1::L2) P3 ->
    LJ_provable (P2::L2) P3 ->
    LJ_provable (L1++L2) P3.
Proof.
intros P1 P2 P3 L1 L2 Hcut1 Hcut2 HC HP1 HP2.
remember (PPdisj P1 P2) as P4 in HC.
induction HC.
- rewrite <-H.
  apply IHHC,HeqP4.
- apply LJ_weak,IHHC,HeqP4.
- apply LJ_contr,IHHC,HeqP4.
- rewrite HeqP4; simpl.
  apply LJ_disj_antecedent.
  + exact HP1.
  + exact HP2.
- setoid_replace ((PPbot::nil)++L2) with (L2++(PPbot::nil)); [|perm].
  apply LJ_weakN.
  apply LJ_exfalso.
- apply LJ_impl_antecedent.
  + change (LJ_provable (L1++L2) P0).
    setoid_replace (L1++L2) with (L2++L1); [|perm].
    apply LJ_weakN.
    exact HC1.
  + change (LJ_provable (P4::L1++L2) P3).
    apply IHHC2,HeqP4.
- congruence.
- apply LJ_conj_antecedent.
  apply IHHC,HeqP4.
- congruence.
- apply LJ_disj_antecedent.
  + apply IHHC1,HeqP4.
  + apply IHHC2,HeqP4.
- apply Hcut1.
  + replace P1 with P0 by congruence.
    exact HC.
  + exact HP1.
- apply Hcut2.
  + replace P2 with P4 by congruence.
    exact HC.
  + exact HP2.
Qed. 

Lemma LJ_cut_general:
  forall P1 P2 L1 L2 n,
    LJ_provable L1 P1 ->
    LJ_provable (replicate n P1++L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 KL2 n HPrL HPrR.
remember (replicate n KP1 ++ KL2) as KL3 in HPrR.
assert (HKL3: Permutation KL3 (replicate n KP1 ++ KL2)) by (rewrite HeqKL3; reflexivity).
clear HeqKL3.
revert KL1 KL2 n HKL3 HPrL.
induction HPrR.
- intros KL1 KL2 n HKL3 HPrL.
  apply IHHPrR with (n:=n).
  + transitivity L2; tauto.
  + exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect in HKL3.
  destruct HKL3 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + destruct n as [|n]; [contradict PrB|].
    apply IHHPrR with (n:=n).
    * exact PrB.
    * exact HPrL.
  + rewrite PrC.
    LJ_reorder_antecedent (P1::KL1++KL2').
    apply LJ_weak.
    apply IHHPrR with (n:=n).
    * exact PrD.
    * exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect in HKL3.
  destruct HKL3 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + destruct n as [|n]; [contradict PrB|].
    apply IHHPrR with (n:=S (S n)).
    * rewrite PrA.
      do 2 apply Permutation_cons.
      exact PrB.
    * exact HPrL.
  + rewrite PrC.
    LJ_reorder_antecedent (P1::KL1++KL2').
    apply LJ_contr.
    LJ_reorder_antecedent (KL1++(P1::P1::KL2')).
    apply IHHPrR with (n:=n).
    * rewrite PrD.
      perm.
    * exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect_nil in HKL3.
  destruct HKL3 as [(PrA,(PrB,PrC)) | (PrD,PrE)].
  + rewrite PrA,PrC,app_nil_r.
    exact HPrL.
  + rewrite PrE.
    apply LJ_weakN.
    apply LJ_axiom.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect_nil in HKL3.
  destruct HKL3 as [(PrA,(PrB,PrC)) | (PrD,PrE)].
  + rewrite PrC,app_nil_r.
    apply LJ_bot_elim.
    rewrite PrA.
    exact HPrL.
  + rewrite PrE.
    apply LJ_weakN.
    apply LJ_exfalso.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect in HKL3.
  destruct HKL3 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + destruct n as [|n]; [contradict PrB|].
    {
      LJ_reorder_antecedent (KL1++KL2).
      do 2 apply LJ_contrN.
      LJ_reorder_antecedent (KL2++KL1++KL1++KL1).
      apply LJ_contrN.
      LJ_reorder_antecedent (((KL1++KL2)++KL1)++(KL1++KL2)).
      apply HI_rank with (y:=P2) (n:=1).
      - rewrite <-PrA.
        left;right;exists P1; reflexivity.
      - apply HI_rank with (y:=P1) (n:=1).
        + rewrite <-PrA.
          left;left;exists P2; reflexivity.
        + apply IHHPrR1 with (n:=n).
          * exact PrB.
          * exact HPrL.
        + apply LJ_impl_elim.
          rewrite PrA.
          exact HPrL.
      - simpl.
        LJ_reorder_antecedent (KL1 ++ (P2::KL2)).
        apply IHHPrR2 with (n:=n).
        + rewrite PrB; perm.
        + exact HPrL.
    }
  + rewrite PrC.
    LJ_reorder_antecedent (PPimpl P1 P2 :: KL1 ++ KL2').
    {
      apply LJ_impl_antecedent.
      - apply IHHPrR1 with (n:=n).
        + exact PrD.
        + exact HPrL.
      - LJ_reorder_antecedent (KL1 ++ P2 :: KL2').
        apply IHHPrR2 with (n:=n).
        + rewrite PrD; perm.
        + exact HPrL.
    }
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_impl_succedent.
  LJ_reorder_antecedent (KL1 ++ P1 :: KL2).
  apply IHHPrR with (n:=n).
  + rewrite HKL3; perm.
  + exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect in HKL3.
  destruct HKL3 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + destruct n as [|n]; [contradict PrB|].
    {
      do 2 apply LJ_contrN.
      apply HI_rank with (y:=P2) (n:=1).
      - rewrite <-PrA.
        right;left;right;exists P1;reflexivity.
      - apply LJ_conj_elim_r with (P1:=P1).
        rewrite PrA.
        exact HPrL.
      - simpl; LJ_reorder_antecedent (KL1 ++ P2 :: KL1 ++ KL2).
        apply HI_rank with (y:=P1) (n:=1).
        + rewrite <-PrA.
          right;left;left;exists P2;reflexivity.
        + apply LJ_conj_elim_l with (P2:=P2).
          rewrite PrA.
          exact HPrL.
        + simpl; LJ_reorder_antecedent (KL1 ++ P1 :: P2 :: KL2).
          apply IHHPrR with (n:=n).
          * rewrite PrB; perm.
          * exact HPrL.
    }
  + rewrite PrC.
    LJ_reorder_antecedent (PPconj P1 P2 :: KL1 ++ KL2').
    apply LJ_conj_antecedent.
    LJ_reorder_antecedent (KL1 ++ P1 :: P2 :: KL2').
    apply IHHPrR with (n:=n).
    * rewrite PrD; perm.
    * exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_conj_succedent.
  + apply IHHPrR1 with (n:=n).
    * exact HKL3.
    * exact HPrL.
  + apply IHHPrR2 with (n:=n).
    * exact HKL3.
    * exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_cut_permselect in HKL3.
  destruct HKL3 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + destruct n as [|n]; [contradict PrB|].
    {
      apply LJ_contrN.
      apply LJ_disj_elim2_withcut with (P1:=P1) (P2:=P2).
      - intros PA LA1 LA2 HA1 HA2.
        apply HI_rank with (y:=P1) (n:=1).
        + rewrite <-PrA.
          right;right;left; exists P2; reflexivity.
        + exact HA1.
        + exact HA2.
      - intros PA LA1 LA2 HA1 HA2.
        apply HI_rank with (y:=P2) (n:=1).
        + rewrite <-PrA.
          right;right;right; exists P1; reflexivity.
        + exact HA1.
        + exact HA2.
      - rewrite PrA.
        exact HPrL.
      - LJ_reorder_antecedent (KL1 ++ P1 :: KL2).
        apply IHHPrR1 with (n:=n).
        + rewrite PrB; perm.
        + exact HPrL.
      - LJ_reorder_antecedent (KL1 ++ P2 :: KL2).
        apply IHHPrR2 with (n:=n).
        + rewrite PrB; perm.
        + exact HPrL.
    }
  + rewrite PrC.
    {
      LJ_reorder_antecedent (PPdisj P1 P2 :: KL1 ++ KL2').
      apply LJ_disj_antecedent.
      - LJ_reorder_antecedent (KL1 ++ P1 :: KL2').
        apply IHHPrR1 with (n:=n).
        + rewrite PrD; perm.
        + exact HPrL.
      - LJ_reorder_antecedent (KL1 ++ P2 :: KL2').
        apply IHHPrR2 with (n:=n).
        + rewrite PrD; perm.
        + exact HPrL.
    }
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_disj_succedent_l.
  apply IHHPrR with (n:=n).
  + exact HKL3.
  + exact HPrL.
- intros KL1 KL2 n HKL3 HPrL.
  apply LJ_disj_succedent_r.
  apply IHHPrR with (n:=n).
  + exact HKL3.
  + exact HPrL.
Qed.

Lemma LJ_cut2:
  forall P1 P2 L1 L2,
    LJ_provable L1 P1 ->
    LJ_provable (P1::L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
intros P1 P2 L1 L2.
apply LJ_cut_general with (n:=1).
Qed.

Theorem LJ_cut:
  forall P1 P2 L1,
    LJ_provable L1 P1 ->
    LJ_provable (P1::L1) P2 ->
    LJ_provable L1 P2.
Proof.
intros P1 P2 L1 HPrL HPrR.
rewrite (app_nil_end L1).
apply LJ_contrN.
rewrite app_nil_r.
revert HPrL HPrR.
apply LJ_cut2.
Qed.

Lemma LJ_disj_elim2:
  forall P1 P2 P3 L1 L2,
    LJ_provable L1 (PPdisj P1 P2) ->
    LJ_provable (P1::L2) P3 ->
    LJ_provable (P2::L2) P3 ->
    LJ_provable (L1++L2) P3.
Proof.
intros P1 P2 P3 L1 L2.
apply LJ_disj_elim2_withcut.
- intros PA LA1 LA2.
  apply LJ_cut2.
- intros PA LA1 LA2.
  apply LJ_cut2.
Qed.

Lemma LJ_disj_elim:
  forall P1 P2 P3 L1,
    LJ_provable L1 (PPdisj P1 P2) ->
    LJ_provable (P1::L1) P3 ->
    LJ_provable (P2::L1) P3 ->
    LJ_provable L1 P3.
Proof.
intros P1 P2 P3 L1 HPrL HPrR1 HPrR2.
rewrite (app_nil_end L1).
apply LJ_contrN.
rewrite app_nil_r.
revert HPrL HPrR1 HPrR2.
apply LJ_disj_elim2.
Qed.
