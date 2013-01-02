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
  apply (LJm_perm_antecedent L); [perm|].

Ltac LJm_reorder_succedent L :=
  apply (LJm_perm_succedent L); [perm|].

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

Lemma LJm_disj_succedent:
  forall P1 P2 L1 L2,
    LJm_provable L1 (P1::P2::L2) ->
    LJm_provable L1 (PPdisj P1 P2::L2).
Proof.
intros P1 P2 L1 L2 H.
rewrite <-LJ_LJm_iff.
apply LJ_cut with (P1:=fold_succedent (P1::P2::L2)).
{
  rewrite LJ_LJm_iff.
  exact H.
}
simpl.
apply LJ_disj_antecedent.
- apply LJ_disj_succedent_l.
  apply LJ_disj_succedent_l.
  apply LJ_axiom2.
- apply LJ_disj_antecedent.
  + apply LJ_disj_succedent_l.
    apply LJ_disj_succedent_r.
    apply LJ_axiom2.
  + apply LJ_disj_succedent_r.
    apply LJ_axiom2.
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

Instance PProp_saturated_antecedent_compat:
  Proper (eq ==> @Permutation _ ==> @Permutation _ ==> iff)
    PProp_saturated_antecedent.
Proof.
unfold Proper,respectful.
intros P1 P HP.
rewrite HP; clear P1 HP.
intros AntA AntB HA SucA SucB HS.
split.
- intros H.
  destruct P;
    simpl in H |- *;
    try rewrite <-HA;
    try rewrite <-HS;
    exact H.
- intros H.
  destruct P;
    simpl in H |- *;
    try rewrite HA;
    try rewrite HS;
    exact H.
Qed.

Instance PProp_saturated_succedent_compat:
  Proper (eq ==> @Permutation _ ==> iff)
    PProp_saturated_succedent.
Proof.
unfold Proper,respectful.
intros P1 P HP.
rewrite HP; clear P1 HP.
intros SucA SucB HS.
split.
- intros H.
  destruct P;
    simpl in H |- *;
    try rewrite <-HS;
    exact H.
- intros H.
  destruct P;
    simpl in H |- *;
    try rewrite HS;
    exact H.
Qed.

Lemma PProp_saturated_antecedent_weak_Ant:
  forall P1 P2 Ant Suc,
    PProp_saturated_antecedent P1 Ant Suc ->
    PProp_saturated_antecedent P1 (P2::Ant) Suc.
Proof.
intros [|A1|P1A P1B|P1A P1B|P1A P1B] P2 Ant Suc H; simpl.
- exact I.
- exact I.
- destruct H as [H|H].
  + left; exact H.
  + right; right; exact H.
- destruct H as (HA,HB).
  exact (conj (or_intror HA) (or_intror HB)).
- destruct H as [H|H].
  + left; right; exact H.
  + right; right; exact H.
Qed.

Lemma PProp_saturated_antecedent_weak_Suc:
  forall P1 P2 Ant Suc,
    PProp_saturated_antecedent P1 Ant Suc ->
    PProp_saturated_antecedent P1 Ant (P2::Suc).
Proof.
intros [|A1|P1A P1B|P1A P1B|P1A P1B] P2 Ant Suc H; simpl.
- exact I.
- exact I.
- destruct H as [H|H].
  + left; right; exact H.
  + right; exact H.
- exact H.
- exact H.
Qed.

Lemma PProp_saturated_succedent_weak:
  forall P1 P2 Suc,
    PProp_saturated_succedent P1 Suc ->
    PProp_saturated_succedent P1 (P2::Suc).
Proof.
intros [|A1|P1A P1B|P1A P1B|P1A P1B] P2 Suc H; simpl.
- exact I.
- exact I.
- exact I.
- destruct H as [H|H].
  + left; right; exact H.
  + right; right; exact H.
- destruct H as (HA,HB).
  exact (conj (or_intror HA) (or_intror HB)).
Qed.

Definition LJm_unprovable_saturated(Ant Suc:list PProp):Prop :=
  ~LJm_provable Ant Suc /\
  (forall P1, In P1 Ant -> PProp_saturated_antecedent P1 Ant Suc) /\
  (forall P1, In P1 Suc -> PProp_saturated_succedent P1 Suc).

Lemma LJm_saturate: forall Ant Suc, ~LJm_provable Ant Suc ->
  exists L1 L2, LJm_unprovable_saturated (L1++Ant) (L2++Suc).
Proof.
unfold LJm_unprovable_saturated.
cut (forall LA Ant Suc, ~LJm_provable (LA++Ant) Suc ->
  exists L1 L2,
    ~LJm_provable (L1++LA++Ant) (L2++Suc) /\
    (forall P1, In P1 (L1++Ant) ->
      PProp_saturated_antecedent P1 (L1++LA++Ant) (L2++Suc)) /\
    (forall P1, In P1 (L2++Suc) -> PProp_saturated_succedent P1 (L2++Suc))
).
{
  intros H.
  exact (H nil).
}
intros LA Ant Suc.
revert LA Suc.
induction Ant as (Ant,IHAnt') using
    (well_founded_induction
      (multiset_ordering_wf _ _
        PProp_small_wellfounded)).
destruct Ant as [|AntH AntT].
- cut (forall LA LS Suc, ~LJm_provable LA (LS++Suc) ->
    exists L2,
      ~LJm_provable LA (L2++LS++Suc) /\
      (forall P1, In P1 (L2++Suc) ->
        PProp_saturated_succedent P1 (L2++LS++Suc))
  ).
  {
    intros H.
    intros LA Suc HPrN.
    rewrite app_nil_r in HPrN.
    specialize (H LA nil Suc HPrN).
    rewrite app_nil_r.
    destruct H as (L2,(HA,HB)).
    exists nil,L2.
    split; [|split].
    - exact HA.
    - intros P1 [].
    - exact HB.
  }
  intros LA LS Suc.
  revert LA LS.
  induction Suc as (Suc,IHSuc') using
      (well_founded_induction
        (multiset_ordering_wf _ _
          PProp_small_wellfounded)).
  assert (IHSuc := fun y LA LS H => IHSuc' y H LA LS).
  clear IHSuc'.
  destruct Suc as [|SucH SucT].
  {
    intros LA LS HPrN.
    exists nil.
    split.
    - exact HPrN.
    - intros P1 [].
  }
  intros LA LS HPrN.
  destruct SucH as [|A1|P1 P2|P1 P2|P1 P2].
  + destruct (IHSuc SucT LA (PPbot::LS)) as (L2,(HL2A,HL2B)).
    {
      exists SucT,nil,(PPbot::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      intros HPr.
      contradict HPrN.
      LJm_reorder_succedent (PPbot::LS++SucT).
      exact HPr.
    }
    exists L2.
    split.
    {
      intros HPrC.
      contradict HL2A.
      LJm_reorder_succedent (L2++LS++PPbot::SucT).
      exact HPrC.
    }
    setoid_replace (L2++PPbot::SucT)
        with (PPbot::L2++SucT); [|perm].
    intros P0 [HP0|HP0].
    * rewrite <-HP0.
      exact I.
    * setoid_replace (L2++LS++PPbot::SucT)
          with (L2++(PPbot::LS)++SucT); [|perm].
      apply HL2B,HP0.
  + destruct (IHSuc SucT LA (PPatom A1::LS)) as (L2,(HL2A,HL2B)).
    {
      exists SucT,nil,(PPatom A1::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      intros HPr.
      contradict HPrN.
      LJm_reorder_succedent (PPatom A1::LS++SucT).
      exact HPr.
    }
    exists L2.
    split.
    {
      intros HPrC.
      contradict HL2A.
      LJm_reorder_succedent (L2++LS++PPatom A1::SucT).
      exact HPrC.
    }
    setoid_replace (L2++PPatom A1::SucT)
        with (PPatom A1::L2++SucT); [|perm].
    intros P0 [HP0|HP0].
    * rewrite <-HP0.
      exact I.
    * setoid_replace (L2++LS++PPatom A1::SucT)
          with (L2++(PPatom A1::LS)++SucT); [|perm].
      apply HL2B,HP0.
  + destruct (IHSuc SucT LA (PPimpl P1 P2::LS)) as (L2,(HL2A,HL2B)).
    {
      exists SucT,nil,(PPimpl P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      intros HPr.
      contradict HPrN.
      LJm_reorder_succedent (PPimpl P1 P2::LS++SucT).
      exact HPr.
    }
    exists L2.
    split.
    {
      intros HPrC.
      contradict HL2A.
      LJm_reorder_succedent (L2++LS++PPimpl P1 P2::SucT).
      exact HPrC.
    }
    setoid_replace (L2++PPimpl P1 P2::SucT)
        with (PPimpl P1 P2::L2++SucT); [|perm].
    intros P0 [HP0|HP0].
    * rewrite <-HP0.
      exact I.
    * setoid_replace (L2++LS++PPimpl P1 P2::SucT)
          with (L2++(PPimpl P1 P2::LS)++SucT); [|perm].
      apply HL2B,HP0.
  + destruct (LJm_dec LA (P1::LS++SucT)) as [HPrA|HPrNA].
    * {
        destruct (IHSuc (P2::SucT) LA (PPconj P1 P2::LS)) as (L2,(HL2A,HL2B)).
        {
          exists SucT,(P2::nil),(PPconj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0; clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          apply (PPsmall_conj_r _ (eq_refl _)).
        }
        {
          intros HPrB.
          contradict HPrN.
          LJm_reorder_succedent (PPconj P1 P2::LS++SucT).
          apply LJm_contr_succedent.
          apply LJm_conj_succedent.
          - rewrite perm_swap.
            apply LJm_weak_succedent.
            exact HPrA.
          - LJm_reorder_succedent ((PPconj P1 P2::LS)++P2::SucT).
            exact HPrB.
        }
        exists (P2::L2).
        split.
        {
          intros HPrC.
          contradict HL2A.
          LJm_reorder_succedent (P2::L2++LS++PPconj P1 P2::SucT).
          exact HPrC.
        }
        setoid_replace ((P2::L2)++PPconj P1 P2::SucT)
            with (P2::PPconj P1 P2::L2++SucT); [|perm].
        intros P0 [HP0|[HP0|HP0]].
        * rewrite <-HP0.
          setoid_replace ((P2::L2)++LS++PPconj P1 P2::SucT)
              with (L2++(PPconj P1 P2::LS)++P2::SucT); [|perm].
          apply HL2B.
          rewrite in_app_iff; right.
          apply in_eq.
        * rewrite <-HP0.
          right.
          apply in_eq.
        * setoid_replace ((P2::L2)++LS++PPconj P1 P2::SucT)
              with (L2++(PPconj P1 P2::LS)++P2::SucT); [|perm].
          apply HL2B.
          setoid_replace (L2++P2::SucT) with (P2::L2++SucT); [|perm].
          right.
          exact HP0.
      }
    * {
        destruct (IHSuc (P1::SucT) LA (PPconj P1 P2::LS)) as (L2,(HL2A,HL2B)).
        {
          exists SucT,(P1::nil),(PPconj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0; clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          apply (PPsmall_conj_l _ (eq_refl _)).
        }
        {
          intros HPrA.
          contradict HPrNA.
          apply LJm_contr_succedent.
          LJm_reorder_succedent (P1::LS++P1::SucT).
          rewrite <-LJ_LJm_iff.
          apply LJ_cut with (P1:=fold_succedent (PPconj P1 P2::LS++P1::SucT)).
          {
            rewrite LJ_LJm_iff.
            exact HPrA.
          }
          simpl.
          apply LJ_disj_antecedent.
          - apply LJ_conj_antecedent.
            apply LJ_disj_succedent_l.
            apply LJ_axiom2.
          - apply LJ_disj_succedent_r.
            apply LJ_axiom2.
        }
        exists (P1::L2).
        split.
        {
          intros HPrC.
          contradict HL2A.
          LJm_reorder_succedent (P1::L2++LS++PPconj P1 P2::SucT).
          exact HPrC.
        }
        setoid_replace ((P1::L2)++PPconj P1 P2::SucT)
            with (P1::PPconj P1 P2::L2++SucT); [|perm].
        intros P0 [HP0|[HP0|HP0]].
        * rewrite <-HP0.
          setoid_replace ((P1::L2)++LS++PPconj P1 P2::SucT)
              with (L2++(PPconj P1 P2::LS)++P1::SucT); [|perm].
          apply HL2B.
          rewrite in_app_iff; right.
          apply in_eq.
        * rewrite <-HP0.
          left.
          apply in_eq.
        * setoid_replace ((P1::L2)++LS++PPconj P1 P2::SucT)
              with (L2++(PPconj P1 P2::LS)++P1::SucT); [|perm].
          apply HL2B.
          setoid_replace (L2++P1::SucT) with (P1::L2++SucT); [|perm].
          right.
          exact HP0.
      }
  + destruct (IHSuc (P1::P2::SucT) LA (PPdisj P1 P2::LS)) as (L2,(HL2A,HL2B)).
    {
      exists SucT,(P1::P2::nil),(PPdisj P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[HP0|[]]].
      - rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_disj_l _ (eq_refl _)).
      - rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_disj_r _ (eq_refl _)).
    }
    {
      intros HPr.
      contradict HPrN.
      LJm_reorder_succedent (PPdisj P1 P2::LS++SucT).
      apply LJm_contr_succedent.
      apply LJm_disj_succedent.
      LJm_reorder_succedent (PPdisj P1 P2::LS++P1::P2::SucT).
      exact HPr.
    }
    exists (P1::P2::L2).
    split.
    {
      intros HPrC.
      contradict HL2A.
      LJm_reorder_succedent (P1::P2::L2++LS++PPdisj P1 P2::SucT).
      exact HPrC.
    }
    setoid_replace ((P1::P2::L2)++PPdisj P1 P2::SucT)
        with (PPdisj P1 P2::L2++P1::P2::SucT); [|perm].
    intros P0 [HP0|HP0].
    * {
        rewrite <-HP0.
        split.
        - apply in_eq.
        - right; apply in_eq.
      }
    * setoid_replace ((P1::P2::L2)++LS++PPdisj P1 P2::SucT)
          with (L2++(PPdisj P1 P2::LS)++P1::P2::SucT); [|perm].
      apply HL2B,HP0.
- assert (IHAnt := fun y LA Suc H => IHAnt' y H LA Suc).
  clear IHAnt'.
  intros LA Suc HPrN.
  destruct AntH as [|A1|P1 P2|P1 P2|P1 P2].
  + contradict HPrN.
    LJm_reorder_antecedent (PPbot::LA++AntT).
    apply LJm_exfalso2.
  + destruct (IHAnt AntT (PPatom A1::LA) Suc) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
    {
      exists AntT,nil,(PPatom A1::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [].
    }
    {
      intros HPr.
      contradict HPrN.
      LJm_reorder_antecedent (PPatom A1::LA++AntT).
      exact HPr.
    }
    exists L1,L2.
    split.
    {
      intros HPrA.
      contradict HL1A.
      LJm_reorder_antecedent (L1++LA++PPatom A1::AntT).
      exact HPrA.
    }
    split; [|exact HL1C].
    setoid_replace (L1++PPatom A1::AntT)
        with (PPatom A1::L1++AntT); [|perm].
    intros P0 [HP0|HP0].
    * rewrite <-HP0.
      exact I.
    * setoid_replace (L1++LA++PPatom A1::AntT)
         with (L1++PPatom A1::LA++AntT); [|perm].
      apply HL1B,HP0.
  + destruct (LJm_dec (PPimpl P1 P2::LA++AntT) (P1::Suc)) as [HPrA|HPrNA].
    * destruct (IHAnt (P2::AntT) LA Suc) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
      {
        exists AntT,(P2::nil),(PPimpl P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPimpl P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_impl_r _ (eq_refl _)).
      }
      {
        intros HPrB.
        contradict HPrN.
        LJm_reorder_antecedent (PPimpl P1 P2::LA++AntT).
        apply LJm_contr_antecedent.
        apply LJm_impl_antecedent.
        - exact HPrA.
        - LJm_reorder_antecedent (PPimpl P1 P2::LA++P2::AntT).
          apply LJm_weak_antecedent.
          exact HPrB.
      }
      exists (P2::L1),L2.
      split.
      {
        intros HPrC.
        contradict HL1A.
        LJm_reorder_antecedent (P2::L1++LA++AntT).
        rewrite <-LJ_LJm_iff.
        apply LJ_cut with (P1:=PPimpl P1 P2).
        {
          apply LJ_impl_succedent,LJ_weak,LJ_axiom2.
        }
        rewrite LJ_LJm_iff.
        LJm_reorder_antecedent (P2::L1++LA++PPimpl P1 P2::AntT).
        exact HPrC.
      }
      split; [|exact HL1C].
      setoid_replace ((P2::L1)++PPimpl P1 P2::AntT)
          with (PPimpl P1 P2::L1++P2::AntT); [|perm].
      {
        intros P0 [HP0|HP0].
        - rewrite <-HP0.
          right.
          apply in_eq.
        - setoid_replace ((P2::L1)++LA++PPimpl P1 P2::AntT)
             with (PPimpl P1 P2::L1++LA++P2::AntT); [|perm].
          apply PProp_saturated_antecedent_weak_Ant.
          apply HL1B,HP0.
      }
    * destruct (IHAnt AntT (PPimpl P1 P2::LA) (P1::Suc)) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
      {
        exists AntT,nil,(PPimpl P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [].
      }
      {
        intros HPrA.
        contradict HPrNA.
        exact HPrA.
      }
      exists L1,(P1::L2).
      split.
      {
        intros HPrC.
        contradict HL1A.
        LJm_reorder_antecedent (L1++LA++PPimpl P1 P2::AntT).
        LJm_reorder_succedent (P1::L2++Suc).
        exact HPrC.
      }
      split.
      {
        setoid_replace (L1++PPimpl P1 P2::AntT)
            with (PPimpl P1 P2::L1++AntT); [|perm].
        {
          intros P0 [HP0|HP0].
          - rewrite <-HP0.
            left.
            apply in_eq.
          - setoid_replace (L1++LA++PPimpl P1 P2::AntT)
               with (L1++(PPimpl P1 P2::LA)++AntT); [|perm].
            setoid_replace ((P1::L2)++Suc) with (L2++P1::Suc); [|perm].
            apply HL1B,HP0.
        }
      }
      {
        setoid_replace ((P1::L2)++Suc) with (L2++P1::Suc); [|perm].
        exact HL1C.
      }
  + destruct (IHAnt (P1::P2::AntT) (PPconj P1 P2::LA) Suc) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
      {
        exists AntT,(P1::P2::nil),(PPconj P1 P2::nil).
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
      {
        intros HPr.
        contradict HPrN.
        LJm_reorder_antecedent (PPconj P1 P2::LA++AntT).
        apply LJm_contr_antecedent.
        apply LJm_conj_antecedent.
        LJm_reorder_antecedent (PPconj P1 P2::LA++P1::P2::AntT).
        exact HPr.
      }
      exists (P1::P2::L1),L2.
      split.
      {
        intros HPrC.
        contradict HL1A.
        LJm_reorder_antecedent (P1::P2::L1++LA++PPconj P1 P2::AntT).
        exact HPrC.
      }
      split; [|exact HL1C].
      setoid_replace ((P1::P2::L1)++PPconj P1 P2::AntT)
          with (PPconj P1 P2::L1++P1::P2::AntT); [|perm].
      {
        intros P0 [HP0|HP0].
        - rewrite <-HP0.
          split.
          + apply in_eq.
          + right; apply in_eq.
        - setoid_replace ((P1::P2::L1)++LA++PPconj P1 P2::AntT)
             with (L1++PPconj P1 P2::LA++P1::P2::AntT); [|perm].
          apply HL1B,HP0.
      }
  + destruct (LJm_dec (PPdisj P1 P2::P1::LA++AntT) Suc) as [HPrA|HPrNA].
    * destruct (IHAnt (P2::AntT) (PPdisj P1 P2::LA) Suc) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
      {
        exists AntT,(P2::nil),(PPdisj P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_disj_r _ (eq_refl _)).
      }
      {
        intros HPrB.
        contradict HPrN.
        LJm_reorder_antecedent (PPdisj P1 P2::LA++AntT).
        apply LJm_contr_antecedent.
        apply LJm_disj_antecedent.
        - LJm_reorder_antecedent (PPdisj P1 P2::P1::LA++AntT).
          exact HPrA.
        - LJm_reorder_antecedent (PPdisj P1 P2::LA++P2::AntT).
          exact HPrB.
      }
      exists (P2::L1),L2.
      split.
      {
        intros HPrC.
        contradict HL1A.
        LJm_reorder_antecedent (P2::L1++LA++PPdisj P1 P2::AntT).
        exact HPrC.
      }
      split; [|exact HL1C].
      setoid_replace ((P2::L1)++PPdisj P1 P2::AntT)
          with (PPdisj P1 P2::L1++P2::AntT); [|perm].
      {
        intros P0 [HP0|HP0].
        - rewrite <-HP0.
          right.
          apply in_eq.
        - setoid_replace ((P2::L1)++LA++PPdisj P1 P2::AntT)
             with (L1++PPdisj P1 P2::LA++P2::AntT); [|perm].
          apply HL1B,HP0.
      }
    * destruct (IHAnt (P1::AntT) (PPdisj P1 P2::LA) Suc) as (L1,(L2,(HL1A,(HL1B,HL1C)))).
      {
        exists AntT,(P1::nil),(PPdisj P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P1 P2).
        split.
        { apply in_eq. }
        apply (PPsmall_disj_l _ (eq_refl _)).
      }
      {
        intros HPrA.
        contradict HPrNA.
        LJm_reorder_antecedent (PPdisj P1 P2::LA++P1::AntT).
        exact HPrA.
      }
      exists (P1::L1),L2.
      split.
      {
        intros HPrC.
        contradict HL1A.
        LJm_reorder_antecedent (P1::L1++LA++PPdisj P1 P2::AntT).
        exact HPrC.
      }
      split; [|exact HL1C].
      setoid_replace ((P1::L1)++PPdisj P1 P2::AntT)
          with (PPdisj P1 P2::L1++P1::AntT); [|perm].
      {
        intros P0 [HP0|HP0].
        - rewrite <-HP0.
          left.
          apply in_eq.
        - setoid_replace ((P1::L1)++LA++PPdisj P1 P2::AntT)
             with (L1++PPdisj P1 P2::LA++P1::AntT); [|perm].
          apply HL1B,HP0.
      }
Qed.