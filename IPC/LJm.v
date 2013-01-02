Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.
Require Import MultisetOrdering.
Require Import PProp.
Require Import LJ.
Require DLI.

Inductive LJm_provable : list PProp -> list PProp -> Prop :=
  | LJm_perm_antecedent L1 L2 L3 :
      Permutation L1 L2 ->
      LJm_provable L1 L3 ->
      LJm_provable L2 L3
  | LJm_perm_succedent L1 L2 L3 :
      Permutation L1 L2 ->
      LJm_provable L3 L1 ->
      LJm_provable L3 L2
  | LJm_weak_antecedent P1 L1 L2 :
      LJm_provable L1 L2 ->
      LJm_provable (P1::L1) L2
  | LJm_weak_succedent P1 L1 L2 :
      LJm_provable L1 L2 ->
      LJm_provable L1 (P1::L2)
  | LJm_contr_antecedent P1 L1 L2 :
      LJm_provable (P1::P1::L1) L2 ->
      LJm_provable (P1::L1) L2
  | LJm_contr_succedent P1 L1 L2 :
      LJm_provable L1 (P1::P1::L2) ->
      LJm_provable L1 (P1::L2)
  | LJm_axiom P1 :
      LJm_provable (P1::nil) (P1::nil)
  | LJm_exfalso:
      LJm_provable (PPbot::nil) nil
  | LJm_impl_antecedent P1 P2 L1 L2 :
      LJm_provable L1 (P1::L2) ->
      LJm_provable (P2::L1) L2 ->
      LJm_provable (PPimpl P1 P2::L1) L2
  | LJm_impl_succedent P1 P2 L1 :
      LJm_provable (P1::L1) (P2::nil) ->
      LJm_provable L1 (PPimpl P1 P2::nil)
  | LJm_conj_antecedent P1 P2 L1 L2 :
      LJm_provable (P1::P2::L1) L2 ->
      LJm_provable (PPconj P1 P2::L1) L2
  | LJm_conj_succedent P1 P2 L1 L2 :
      LJm_provable L1 (P1::L2) ->
      LJm_provable L1 (P2::L2) ->
      LJm_provable L1 (PPconj P1 P2::L2)
  | LJm_disj_antecedent P1 P2 L1 L2 :
      LJm_provable (P1::L1) L2 ->
      LJm_provable (P2::L1) L2 ->
      LJm_provable (PPdisj P1 P2::L1) L2
  | LJm_disj_succedent_l P1 P2 L1 L2:
      LJm_provable L1 (P1::L2) ->
      LJm_provable L1 (PPdisj P1 P2::L2)
  | LJm_disj_succedent_r P1 P2 L1 L2 :
      LJm_provable L1 (P2::L2) ->
      LJm_provable L1 (PPdisj P1 P2::L2).

Ltac LJm_reorder_antecedent L :=
  apply (LJm_perm_antecedent _ L); [perm|].

Ltac LJm_reorder_succedent L :=
  apply (LJm_perm_succedent _ L); [perm|].

Instance LJm_provable_compat :
  Proper (@Permutation _==>@Permutation _==>iff) LJm_provable.
Proof.
unfold Proper,respectful.
intros L1A L1B HL1 L2A L2B HL2.
split.
- intros H.
  apply LJm_perm_antecedent with (L1:=L1A).
  { rewrite HL1; reflexivity. }
  apply LJm_perm_succedent with (L1:=L2A).
  { rewrite HL2; reflexivity. }
  exact H.
- intros H.
  apply LJm_perm_antecedent with (L1:=L1B).
  { rewrite HL1; reflexivity. }
  apply LJm_perm_succedent with (L1:=L2B).
  { rewrite HL2; reflexivity. }
  exact H.
Qed.

Lemma LJ_provable_LJm_provable_single:
  forall L1 P1,
    LJ_provable L1 P1 -> LJm_provable L1 (P1::nil).
Proof.
intros KL1 KP1 H.
induction H.
- rewrite <-H.
  exact IHLJ_provable.
- apply LJm_weak_antecedent.
  exact IHLJ_provable.
- apply LJm_contr_antecedent.
  exact IHLJ_provable.
- apply LJm_axiom.
- apply LJm_weak_succedent.
  apply LJm_exfalso.
- apply LJm_impl_antecedent.
  + rewrite perm_swap.
    apply LJm_weak_succedent.
    exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply LJm_impl_succedent.
  exact IHLJ_provable.
- apply LJm_conj_antecedent.
  exact IHLJ_provable.
- apply LJm_conj_succedent.
  + exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply LJm_disj_antecedent.
  + exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply LJm_disj_succedent_l.
  exact IHLJ_provable.
- apply LJm_disj_succedent_r.
  exact IHLJ_provable.
Qed.

Lemma LJ_axiom2:
  forall P1 L1, LJ_provable (P1::L1) P1.
Proof.
intros P1 L1.
induction L1.
- apply LJ_axiom.
- rewrite perm_swap.
  apply LJ_weak,IHL1.
Qed.

Lemma LJ_exfalso2:
  forall P1 L1, LJ_provable (PPbot::L1) P1.
Proof.
intros P1 L1.
induction L1.
- apply LJ_exfalso.
- rewrite perm_swap.
  apply LJ_weak,IHL1.
Qed.

Lemma LJm_axiom2:
  forall P1 L1 L2, LJm_provable (P1::L1) (P1::L2).
Proof.
intros P1 L1 L2.
induction L1.
- induction L2.
  + apply LJm_axiom.
  + rewrite perm_swap.
    apply LJm_weak_succedent.
    apply IHL2.
- rewrite perm_swap.
  apply LJm_weak_antecedent.
  apply IHL1.
Qed.

Lemma LJm_exfalso2:
  forall L1 L2, LJm_provable (PPbot::L1) L2.
Proof.
intros L1 L2.
induction L1.
- induction L2.
  + apply LJm_exfalso.
  + apply LJm_weak_succedent.
    apply IHL2.
- rewrite perm_swap.
  apply LJm_weak_antecedent.
  apply IHL1.
Qed.

Fixpoint fold_succedent(L:list PProp):PProp :=
  match L with
  | nil => PPbot
  | Lh::LT => PPdisj Lh (fold_succedent LT)
  end.

Lemma LJfs_perm:
  forall L1 L2 L3,
    Permutation L1 L2 ->
      LJ_provable L3 (fold_succedent L1) ->
      LJ_provable L3 (fold_succedent L2).
Proof.
intros L1 L2 L3 HL H.
revert L3 H.
induction HL.
- intros L3 H.
  exact H.
- intros L3 H.
  apply LJ_cut with (P1:=fold_succedent (x::l)).
  { exact H. }
  apply LJ_disj_antecedent.
  + apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply IHHL.
    apply LJ_axiom2.
- intros L3 H.
  apply LJ_cut with (P1:=fold_succedent (y::x::l)).
  { exact H. }
  apply LJ_disj_antecedent; [|apply LJ_disj_antecedent].
  + apply LJ_disj_succedent_r.
    apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_disj_succedent_r.
    apply LJ_axiom2.
- intros L3 H.
  apply IHHL2,IHHL1,H.
Qed.

Lemma LJm_provable_LJ_provable:
  forall L1 L2,
    LJm_provable L1 L2 -> LJ_provable L1 (fold_succedent L2).
Proof.
intros KL1 KL2 H.
induction H.
- rewrite <-H.
  exact IHLJm_provable.
- apply LJfs_perm with (L1:=L1).
  { exact H. }
  exact IHLJm_provable.
- apply LJ_weak.
  exact IHLJm_provable.
- apply LJ_disj_succedent_r.
  exact IHLJm_provable.
- apply LJ_contr.
  exact IHLJm_provable.
- apply LJ_cut with (P1:=fold_succedent (P1::P1::L2)).
  { exact IHLJm_provable. }
  apply LJ_disj_antecedent; [|apply LJ_disj_antecedent].
  + apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_axiom2.
- apply LJ_disj_succedent_l.
  apply LJ_axiom.
- apply LJ_exfalso.
- apply LJ_cut with (P1:=fold_succedent (P1::L2)).
  { apply LJ_weak; exact IHLJm_provable1. }
  apply LJ_disj_antecedent.
  + rewrite perm_swap.
    apply LJ_impl_antecedent.
    { apply LJ_axiom2. }
    rewrite perm_swap.
    apply LJ_weak.
    exact IHLJm_provable2.
  + apply LJ_axiom2.
- apply LJ_disj_succedent_l.
  apply LJ_impl_succedent.
  apply LJ_cut with (P1:=fold_succedent (P2::nil)).
  { exact IHLJm_provable. }
  apply LJ_disj_antecedent.
  { apply LJ_axiom2. }
  apply LJ_exfalso2.
- apply LJ_conj_antecedent.
  exact IHLJm_provable.
- apply LJ_cut with (P1:=fold_succedent (P1::L2)).
  { exact IHLJm_provable1. }
  apply LJ_disj_antecedent.
  + apply LJ_cut with (P1:=fold_succedent (P2::L2)).
    { apply LJ_weak; exact IHLJm_provable2. }
    apply LJ_disj_antecedent.
    * apply LJ_disj_succedent_l.
      apply LJ_conj_succedent.
      { apply LJ_weak,LJ_axiom2. }
      apply LJ_axiom2.
    * apply LJ_disj_succedent_r.
      apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_axiom2.
- apply LJ_disj_antecedent.
  + exact IHLJm_provable1.
  + exact IHLJm_provable2.
- apply LJ_cut with (P1:=fold_succedent (P1::L2)).
  { exact IHLJm_provable. }
  apply LJ_disj_antecedent.
  + apply LJ_disj_succedent_l.
    apply LJ_disj_succedent_l.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_axiom2.
- apply LJ_cut with (P1:=fold_succedent (P2::L2)).
  { exact IHLJm_provable. }
  apply LJ_disj_antecedent.
  + apply LJ_disj_succedent_l.
    apply LJ_disj_succedent_r.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_axiom2.
Qed.

Lemma LJ_LJm_iff_single:
  forall P1 L1, LJ_provable L1 P1 <-> LJm_provable L1 (P1::nil).
Proof.
intros P1 L1.
split.
- apply LJ_provable_LJm_provable_single.
- intros H.
  cut (LJ_provable L1 (PPdisj P1 PPbot)).
  {
    intros HH.
    apply LJ_cut with (P1:=PPdisj P1 PPbot).
    { exact HH. }
    apply LJ_disj_antecedent.
    - apply LJ_axiom2.
    - apply LJ_exfalso2.
  }
  revert H.
  apply LJm_provable_LJ_provable.
Qed.

Lemma LJm_weak_succedent_single:
  forall P1 L1 L2,
    LJm_provable L1 (P1::nil) -> LJm_provable L1 (P1::L2).
Proof.
intros P1 L1 L2 H.
induction L2.
- exact H.
- rewrite perm_swap.
  apply LJm_weak_succedent.
  exact IHL2.
Qed.

Lemma LJ_provable_LJm_provable:
  forall L1 L2,
    LJ_provable L1 (fold_succedent L2) -> LJm_provable L1 L2.
Proof.
intros L1 L2.
revert L1.
induction L2.
- intros L1 H.
  simpl in H.
  remember PPbot as P1.
  induction H.
  + rewrite <-H.
    apply IHLJ_provable,HeqP1.
  + apply LJm_weak_antecedent.
    apply IHLJ_provable,HeqP1.
  + apply LJm_contr_antecedent.
    apply IHLJ_provable,HeqP1.
  + rewrite HeqP1.
    apply LJm_exfalso.
  + apply LJm_exfalso.
  + apply LJm_impl_antecedent.
    * apply LJ_provable_LJm_provable_single.
      exact H.
    * apply IHLJ_provable2,HeqP1.
  + congruence.
  + apply LJm_conj_antecedent.
    apply IHLJ_provable,HeqP1.
  + congruence.
  + apply LJm_disj_antecedent.
    * apply IHLJ_provable1,HeqP1.
    * apply IHLJ_provable2,HeqP1.
  + congruence.
  + congruence.
- intros L1 H.
  simpl in H.
  remember (PPdisj a (fold_succedent L2)) as L3.
  induction H.
  + rewrite <-H.
    apply IHLJ_provable,HeqL3.
  + apply LJm_weak_antecedent.
    apply IHLJ_provable,HeqL3.
  + apply LJm_contr_antecedent.
    apply IHLJ_provable,HeqL3.
  + rewrite HeqL3.
    apply LJm_disj_antecedent.
    * apply LJm_axiom2.
    * apply LJm_weak_succedent.
      apply IHL2.
      apply LJ_axiom.
  + apply LJm_exfalso2.
  + apply LJm_impl_antecedent.
    * apply LJm_weak_succedent_single.
      apply LJ_provable_LJm_provable_single.
      exact H.
    * apply IHLJ_provable2,HeqL3.
  + congruence.
  + apply LJm_conj_antecedent.
    apply IHLJ_provable,HeqL3.
  + congruence.
  + apply LJm_disj_antecedent.
    * apply IHLJ_provable1,HeqL3.
    * apply IHLJ_provable2,HeqL3.
  + replace a with P1 by congruence.
    apply LJm_weak_succedent_single.
    apply LJ_provable_LJm_provable_single.
    exact H.
  + apply LJm_weak_succedent.
    apply IHL2.
    replace (fold_succedent L2) with P2 by congruence.
    exact H.
Qed.

Lemma LJ_LJm_iff:
  forall L1 L2, LJ_provable L1 (fold_succedent L2) <-> LJm_provable L1 L2.
Proof.
intros L1 L2.
split.
- apply LJ_provable_LJm_provable.
- apply LJm_provable_LJ_provable.
Qed.

Lemma LJm_dec: forall L1 L2, {LJm_provable L1 L2} + {~LJm_provable L1 L2}.
Proof.
intros L1 L2.
destruct (DLI.LJ_dec (fold_succedent L2) L1) as [HPr|HPrN].
- left.
  rewrite <-LJ_LJm_iff.
  exact HPr.
- right.
  rewrite <-LJ_LJm_iff.
  exact HPrN.
Qed.

Definition PProp_saturated_antecedent(P1:PProp) (Ant Suc:list PProp):Prop :=
  match P1 with
  | PPbot => True
  | PPatom _ => True
  | PPimpl P1A P1B => In P1A Suc \/ In P1B Ant
  | PPconj P1A P1B => In P1A Ant /\ In P1B Ant
  | PPdisj P1A P1B => In P1A Ant \/ In P1B Ant
  end.

Definition PProp_saturated_succedent(P1:PProp) (Suc:list PProp):Prop :=
  match P1 with
  | PPbot => True
  | PPatom _ => True
  | PPimpl _ _ => True
  | PPconj P1A P1B => In P1A Suc \/ In P1B Suc
  | PPdisj P1A P1B => In P1A Suc /\ In P1B Suc
  end.

Definition LJm_unprovable_saturated(Ant Suc:list PProp):Prop :=
  ~LJm_provable Ant Suc /\
  (forall P1, In P1 Ant -> PProp_saturated_antecedent P1 Ant Suc) /\
  (forall P1, In P1 Suc -> PProp_saturated_succedent P1 Suc).

Lemma LJm_saturate: forall Ant Suc, ~LJm_provable Ant Suc ->
  exists L1 L2, LJm_unprovable_saturated (L1++Ant) (L2++Suc).
Proof.
intros Ant Suc HPrN.
remember Ant as Ant' in |-.
remember Suc as Suc' in |-.
unfold LJm_unprovable_saturated.
cut (exists L1 L2,
  ~LJm_provable (L1++Ant) (L2++Suc) /\
  (forall P1, In P1 (L1++Ant') -> PProp_saturated_antecedent P1 (L1++Ant) (L2++Suc)) /\
  (forall P1, In P1 (L2++Suc') -> PProp_saturated_succedent P1 (L2++Suc))).
{
  intros (L1,(L2,H)).
  exists L1,L2.
  rewrite HeqAnt',HeqSuc' in H.
  exact H.
}
clear HeqAnt' HeqSuc'.
remember (Ant'++Suc') as KL.
revert Ant' Suc' HeqKL.
induction KL as (KL,IHKL) using
    (well_founded_induction
      (multiset_ordering_wf _ _
        PProp_small_wellfounded)).
rename IHKL into IHKL'.
assert (IHKL:=fun Ant' Suc' H0 => IHKL' _ H0 Ant' Suc' (eq_refl _)).
clear IHKL'.
intros Ant' Suc' HeqKL.
rewrite HeqKL in * |- *; clear KL HeqKL.
destruct Ant' as [|[|A1|P1 P2|P1 P2|P1 P2] AntT].
- destruct Suc' as [|[|A1|P1 P2|P1 P2|P1 P2] SucT].
  + exists nil,nil.
    split.
    { exact HPrN. }
    split.
    * intros P1 [].
    * intros P1 [].
  + destruct (IHKL nil SucT) as (L1,(L2,(HA,(HB,HC)))).
    {
      exists SucT,nil,(PPbot::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      exists L1,L2.
      split.
      { exact HA. }
      {
        split.
        - exact HB.
        - setoid_replace (L2++PPbot::SucT) with (PPbot::L2++SucT); [|perm].
          intros P1 [HP1|HP1].
          + rewrite <-HP1.
            exists.
          + apply HC,HP1.
      }
    }
  + destruct (IHKL nil SucT) as (L1,(L2,(HA,(HB,HC)))).
    {
      exists SucT,nil,(PPatom A1::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      exists L1,L2.
      split.
      { exact HA. }
      {
        split.
        - exact HB.
        - setoid_replace (L2++PPatom A1::SucT) with (PPatom A1::L2++SucT); [|perm].
          intros P1 [HP1|HP1].
          + rewrite <-HP1.
            exists.
          + apply HC,HP1.
      }
    }
  + destruct (IHKL nil SucT) as (L1,(L2,(HA,(HB,HC)))).
    {
      exists SucT,nil,(PPimpl P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      exists L1,L2.
      split.
      { exact HA. }
      {
        split.
        - exact HB.
        - setoid_replace (L2++PPimpl P1 P2::SucT) 
              with (PPimpl P1 P2::L2++SucT); [|perm].
          intros P0 [HP0|HP0].
          + rewrite <-HP0.
            exists.
          + apply HC,HP0.
      }
    }
  + destruct (IHKL nil (P1::P2::SucT)) as (L1,(L2,(HA,(HB,HC)))).
    {
      exists SucT,(P1::P2::nil),(PPconj P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[HP0|[]]].
      - rewrite <-HP0; clear P0 HP0.
        exists (PPconj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_conj_l _ (eq_refl _)).
      - rewrite <-HP0; clear P0 HP0.
        exists (PPconj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_conj_r _ (eq_refl _)).
    }
    destruct (LJm_dec (L1++Ant) (P1::L2++Suc)) as [HPrA|HPrNA].
    * {
        exists L1,(P2::L2).
        split.
        {
          intros HPrB.
          contradict HA.
          
        }
        split.
        * exact HB.
        * {
            setoid_replace (L2++P1::P2::SucT) 
                with (P1::P2::L2++SucT) in HC; [|perm].
            setoid_replace (L2++PPconj P1 P2::SucT) 
                with (PPconj P1 P2::L2++SucT); [|perm].
            intros P0 [HP0|HP0].
            * rewrite <-HP0.
              simpl.
              exists.
            * apply HC,HP1.
          }
      }
    *
  +
-
-
-
-
-
Qed.