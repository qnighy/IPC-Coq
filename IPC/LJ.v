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
      LJ_provable (P1::L1) P2 ->
      LJ_provable (P1::P1::L1) P2
  | LJ_axiom P1 :
      LJ_provable (P1::nil) P1
  | LJ_exfalso P1 :
      LJ_provable (PPbot::nil) P1
  | LJ_impl_antecedent P1 P2 P3 L1 :
      LJ_provable (PPimpl P1 P2::L1) P1 ->
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

Inductive LJ_step
    (P:list PProp -> PProp -> Prop)
    (Ant:list PProp) (Suc:PProp) : Prop :=
  | LJ_step_perm L1 :
      P L1 Suc ->
      Permutation Ant L1 ->
      LJ_step P Ant Suc
  | LJ_step_weak P1 L1 :
      P L1 Suc ->
      Permutation Ant (P1::L1) ->
      LJ_step P Ant Suc
  | LJ_step_contr P1 L1 :
      P (P1::L1) Suc ->
      Permutation Ant (P1::P1::L1) ->
      LJ_step P Ant Suc
  | LJ_step_axiom :
      Permutation Ant (Suc::nil) ->
      LJ_step P Ant Suc
  | LJ_step_exfalso :
      Permutation Ant (PPbot::nil) ->
      LJ_step P Ant Suc
  | LJ_step_impl_antecedent P1 P2 L1 :
      P (PPimpl P1 P2::L1) P1 ->
      P (P2::L1) Suc ->
      Permutation Ant (PPimpl P1 P2::L1) ->
      LJ_step P Ant Suc
  | LJ_step_impl_succedent P1 P2 :
      P (P1::Ant) P2 ->
      Suc = (PPimpl P1 P2) ->
      LJ_step P Ant Suc
  | LJ_step_conj_antecedent P1 P2 L1 :
      P (P1::P2::L1) Suc ->
      Permutation Ant (PPconj P1 P2::L1) ->
      LJ_step P Ant Suc
  | LJ_step_conj_succedent P1 P2 :
      P Ant P1 ->
      P Ant P2 ->
      Suc = (PPconj P1 P2) ->
      LJ_step P Ant Suc
  | LJ_step_disj_antecedent P1 P2 L1 :
      P (P1::L1) Suc ->
      P (P2::L1) Suc ->
      Permutation Ant (PPdisj P1 P2::L1) ->
      LJ_step P Ant Suc
  | LJ_step_disj_succedent_l P1 P2 :
      P Ant P1 ->
      Suc = (PPdisj P1 P2) ->
      LJ_step P Ant Suc
  | LJ_step_disj_succedent_r P1 P2 :
      P Ant P2 ->
      Suc = (PPdisj P1 P2) ->
      LJ_step P Ant Suc.

Arguments LJ_step_perm [P] [Ant] [Suc] L1 IHs1 HL.
Arguments LJ_step_weak [P] [Ant] [Suc] P1 L1 IHs1 HL.
Arguments LJ_step_contr [P] [Ant] [Suc] P1 L1 IHs1 HL.
Arguments LJ_step_axiom [P] [Ant] [Suc] HL.
Arguments LJ_step_exfalso [P] [Ant] [Suc] HL.
Arguments LJ_step_impl_antecedent [P] [Ant] [Suc] P1 P2 L1 IHs1 IHs2 HL.
Arguments LJ_step_impl_succedent [P] [Ant] [Suc] P1 P2 IHs1 HP.
Arguments LJ_step_conj_antecedent [P] [Ant] [Suc] P1 P2 L1 IHs1 HL.
Arguments LJ_step_conj_succedent [P] [Ant] [Suc] P1 P2 IHs1 IHs2 HP.
Arguments LJ_step_disj_antecedent [P] [Ant] [Suc] P1 P2 L1 IHs1 IHs2 HL.
Arguments LJ_step_disj_succedent_l [P] [Ant] [Suc] P1 P2 IHs1 HP.
Arguments LJ_step_disj_succedent_r [P] [Ant] [Suc] P1 P2 IHs1 HP.

Lemma LJ_step_induction:
  forall(P:list PProp -> PProp -> Prop),
    (forall Ant' Suc', LJ_step P Ant' Suc' -> LJ_provable Ant' Suc' -> P Ant' Suc') ->
    forall(Ant:list PProp) (Suc:PProp), 
      LJ_provable Ant Suc -> P Ant Suc.
Proof.
intros P HInd Ant Suc HPr.
induction HPr.
- apply HInd.
  + apply (LJ_step_perm L1).
    * exact IHHPr.
    * symmetry.
      exact H.
  + apply (LJ_perm P1 L1).
    * exact H.
    * exact HPr.
- apply HInd.
  + apply (LJ_step_weak P1 L1).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_weak P1 P2 L1).
    * exact HPr.
- apply HInd.
  + apply (LJ_step_contr P1 L1).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_contr P1 P2 L1).
    * exact HPr.
- apply HInd.
  + apply (LJ_step_axiom).
    * reflexivity.
  + apply (LJ_axiom P1).
- apply HInd.
  + apply (LJ_step_exfalso).
    * reflexivity.
  + apply (LJ_exfalso P1).
- apply HInd.
  + apply (LJ_step_impl_antecedent P1 P2 L1).
    * exact IHHPr1.
    * exact IHHPr2.
    * reflexivity.
  + apply (LJ_impl_antecedent P1 P2 P3 L1).
    * exact HPr1.
    * exact HPr2.
- apply HInd.
  + apply (LJ_step_impl_succedent P1 P2).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_impl_succedent P1 P2 L1).
    * exact HPr.
- apply HInd.
  + apply (LJ_step_conj_antecedent P1 P2 L1).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_conj_antecedent P1 P2 P3 L1).
    * exact HPr.
- apply HInd.
  + apply (LJ_step_conj_succedent P1 P2).
    * exact IHHPr1.
    * exact IHHPr2.
    * reflexivity.
  + apply (LJ_conj_succedent P1 P2 L1).
    * exact HPr1.
    * exact HPr2.
- apply HInd.
  + apply (LJ_step_disj_antecedent P1 P2 L1).
    * exact IHHPr1.
    * exact IHHPr2.
    * reflexivity.
  + apply (LJ_disj_antecedent P1 P2 P3 L1).
    * exact HPr1.
    * exact HPr2.
- apply HInd.
  + apply (LJ_step_disj_succedent_l P1 P2).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_disj_succedent_l P1 P2 L1).
    * exact HPr.
- apply HInd.
  + apply (LJ_step_disj_succedent_r P1 P2).
    * exact IHHPr.
    * reflexivity.
  + apply (LJ_disj_succedent_r P1 P2 L1).
    * exact HPr.
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

Lemma LJ_conj_elim_l: forall P1 P2 L1, LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P1.
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
  setoid_replace (P1::P2::nil) with (P2::P1::nil); [|perm].
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

Lemma LJ_conj_elim_r: forall P1 P2 L1, LJ_provable L1 (PPconj P1 P2) -> LJ_provable L1 P2.
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

Fixpoint replicate{A:Type} (n:nat) (a:A):list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Theorem LJ_cut_general:
  forall P1 P2 L1 L2 n,
    LJ_provable L1 P1 ->
    LJ_provable (replicate n P1++L2) P2 ->
    LJ_provable (L1++L2) P2.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 KL2 n HPrL HPrR.
induction HPrR using LJ_step_induction.


induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 KL2 n HPrL HPrR.
apply (LJ_step_induction KL1 KP1
  (fun Ant Suc =>
    LJ_provable Ant Suc ->
    LJ_provable (replicate n Suc ++ KL2) KP2 ->
    LJ_provable (Ant ++ KL2) KP2) HPrL); [ | | exact HPrL | exact HPrR ].
{
  unfold Proper,respectful.
  intros L1 L2 HL P1 P2 HP.
  rewrite HL,HP.
  reflexivity.
}
intros KL3 KP3 HI_L HPrL2 HPrR2.
apply (LJ_step_induction (replicate n KP3 ++ KL2) KP2
  (fun Ant Suc =>
    LJ_provable Ant Suc ->
    LJ_provable (KL3 ++ KL2) KP2) HPrR2); [ | | exact HPrR2 ].
{
  unfold Proper,respectful.
  intros L1 L2 HL P1 P2 HP.
  rewrite HL,HP.
  reflexivity.
}
intros KL4 KP4 HI_R HPrR3.
destruct HI_R.
- apply H.
Qed.