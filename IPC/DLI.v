Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import omega.Omega.
Require Import MyPermutations.
Require Import PProp.
Require Import DLJ.
Require Import MultisetOrdering.

(* Dyckhoff's LJT *)
Inductive DLI_provable : list PProp -> PProp -> Prop :=
  | DLI_perm P1 L1 L2 :
      Permutation L1 L2 ->
      DLI_provable L1 P1 ->
      DLI_provable L2 P1
  | DLI_axiom P1 L1 :
      DLI_provable (P1::L1) P1
  | DLI_exfalso P1 L1 :
      DLI_provable (PPbot::L1) P1
  | DLI_impl_antecedent_atom A1 P1 P2 L1 :
      DLI_provable (P1::PPatom A1::L1) P2 ->
      DLI_provable (PPimpl (PPatom A1) P1::PPatom A1::L1) P2
  | DLI_impl_antecedent_impl P1 P2 P3 P4 L1 :
      DLI_provable (PPimpl P3 P1::L1) (PPimpl P2 P3) ->
      DLI_provable (P1::L1) P4 ->
      DLI_provable (PPimpl (PPimpl P2 P3) P1::L1) P4
  | DLI_impl_antecedent_conj P1 P2 P3 P4 L1 :
      DLI_provable (PPimpl P2 (PPimpl P3 P1)::L1) P4 ->
      DLI_provable (PPimpl (PPconj P2 P3) P1::L1) P4
  | DLI_impl_antecedent_disj P1 P2 P3 P4 L1 :
      DLI_provable (PPimpl P2 P1::PPimpl P3 P1::L1) P4 ->
      DLI_provable (PPimpl (PPdisj P2 P3) P1::L1) P4
  | DLI_impl_succedent P1 P2 L1 :
      DLI_provable (P1::L1) P2 ->
      DLI_provable L1 (PPimpl P1 P2)
  | DLI_conj_antecedent P1 P2 P3 L1 :
      DLI_provable (P1::P2::L1) P3 ->
      DLI_provable (PPconj P1 P2::L1) P3
  | DLI_conj_succedent P1 P2 L1 :
      DLI_provable L1 P1 ->
      DLI_provable L1 P2 ->
      DLI_provable L1 (PPconj P1 P2)
  | DLI_disj_antecedent P1 P2 P3 L1 :
      DLI_provable (P1::L1) P3 ->
      DLI_provable (P2::L1) P3 ->
      DLI_provable (PPdisj P1 P2::L1) P3
  | DLI_disj_succedent_l P1 P2 L1 :
      DLI_provable L1 P1 ->
      DLI_provable L1 (PPdisj P1 P2)
  | DLI_disj_succedent_r P1 P2 L1 :
      DLI_provable L1 P2 ->
      DLI_provable L1 (PPdisj P1 P2).

Ltac DLI_reorder_antecedent L :=
  apply (DLI_perm _ L); [perm|].

Instance DLI_provable_compat : Proper (@Permutation _==>eq==>iff) DLI_provable.
Proof.
unfold Proper,respectful.
intros L1 L2 HL P1 P2 HP.
split.
- intros H.
  rewrite <-HP.
  exact (DLI_perm P1 L1 L2 HL H).
- intros H.
  rewrite ->HP.
  exact (DLI_perm P2 L2 L1 (Permutation_sym HL) H).
Qed.

Lemma DLI_weak: forall P1 P2 L1, DLI_provable L1 P2 -> DLI_provable (P1::L1) P2.
Proof.
intros KP1 KP2 KL1 H.
remember KL1 as KL2 in H.
apply eq_then_Permutation in HeqKL2.
revert KP1 KL1 HeqKL2.
induction H.
- intros KP1 KL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2; reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_axiom.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_exfalso.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  DLI_reorder_antecedent (PPimpl (PPatom A1) P1 :: PPatom A1 :: KP1 :: L1).
  apply DLI_impl_antecedent_atom.
  DLI_reorder_antecedent (KP1 :: P1 :: PPatom A1 :: L1).
  apply IHDLI_provable.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_impl_antecedent_impl.
  + rewrite perm_swap.
    apply IHDLI_provable1.
    reflexivity.
  + rewrite perm_swap.
    apply IHDLI_provable2.
    reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_impl_antecedent_conj.
  rewrite perm_swap.
  apply IHDLI_provable.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_impl_antecedent_disj.
  DLI_reorder_antecedent (KP1 :: PPimpl P2 P1 :: PPimpl P3 P1 :: L1).
  apply IHDLI_provable.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  apply DLI_impl_succedent.
  rewrite perm_swap.
  apply IHDLI_provable.
  rewrite HeqKL2.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_conj_antecedent.
  DLI_reorder_antecedent (KP1 :: P1 :: P2 :: L1).
  apply IHDLI_provable.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  apply DLI_conj_succedent.
  + apply IHDLI_provable1.
    reflexivity.
  + apply IHDLI_provable2.
    reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  rewrite perm_swap.
  apply DLI_disj_antecedent.
  + rewrite perm_swap.
    apply IHDLI_provable1.
    reflexivity.
  + rewrite perm_swap.
    apply IHDLI_provable2.
    reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  apply DLI_disj_succedent_l.
  apply IHDLI_provable.
  reflexivity.
- intros KP1 KL1 HeqKL2.
  rewrite <-HeqKL2.
  apply DLI_disj_succedent_r.
  apply IHDLI_provable.
  reflexivity.
Qed.

Record DLJ_antecedent_irreducible(L1:list PProp):Prop
    :=
{
  DLJ_irred_bot:
    In PPbot L1 -> False;
  DLJ_irred_impl:
    forall A1 P1, In (PPimpl (PPatom A1) P1) L1 -> In (PPatom A1) L1 -> False;
  DLJ_irred_conj:
    forall P1 P2, In (PPconj P1 P2) L1 -> False;
  DLJ_irred_disj:
    forall P1 P2, In (PPdisj P1 P2) L1 -> False
}.

Instance DLJ_antecedent_irreducible_compat :
  Proper (@Permutation _==>iff) DLJ_antecedent_irreducible.
Proof.
unfold Proper,respectful.
assert (HH:
  forall L1 L2, Permutation L1 L2 ->
    DLJ_antecedent_irreducible L1 -> DLJ_antecedent_irreducible L2).
{
  intros L1 L2 HL (Hb,Hi,Hc,Hd).
  split.
  - rewrite <-HL.
    apply Hb.
  - intros A1 P1.
    rewrite <-HL.
    apply Hi.
  - intros P1 P2.
    rewrite <-HL.
    apply Hc.
  - intros P1 P2.
    rewrite <-HL.
    apply Hd.
}
intros L1 L2 HL.
split.
- apply HH.
  exact HL.
- apply HH.
  symmetry.
  exact HL.
Qed.

Inductive DLJ_provable_sensible : list PProp -> PProp -> Prop :=
  | DLJ_perm_sensible P1 L1 L2 :
      Permutation L1 L2 ->
      DLJ_provable_sensible L1 P1 ->
      DLJ_provable_sensible L2 P1
  | DLJ_axiom_sensible P1 L1 :
      DLJ_provable_sensible (P1::L1) P1
  | DLJ_exfalso_sensible P1 L1 :
      DLJ_provable_sensible (PPbot::L1) P1
  | DLJ_impl_antecedent_sensible P1 P2 P3 L1 :
      match P1 with
      | PPatom _ => False
      | _ => True
      end ->
      DLJ_provable (PPimpl P1 P2::L1) P1 ->
      DLJ_provable (P2::L1) P3 ->
      DLJ_provable_sensible (PPimpl P1 P2::L1) P3
  | DLJ_impl_succedent_sensible P1 P2 L1 :
      DLJ_provable (P1::L1) P2 ->
      DLJ_provable_sensible L1 (PPimpl P1 P2)
  | DLJ_conj_antecedent_sensible P1 P2 P3 L1 :
      DLJ_provable (P1::P2::L1) P3 ->
      DLJ_provable_sensible (PPconj P1 P2::L1) P3
  | DLJ_conj_succedent_sensible P1 P2 L1 :
      DLJ_provable L1 P1 ->
      DLJ_provable L1 P2 ->
      DLJ_provable_sensible L1 (PPconj P1 P2)
  | DLJ_disj_antecedent_sensible P1 P2 P3 L1 :
      DLJ_provable (P1::L1) P3 ->
      DLJ_provable (P2::L1) P3 ->
      DLJ_provable_sensible (PPdisj P1 P2::L1) P3
  | DLJ_disj_succedent_l_sensible P1 P2 L1 :
      DLJ_provable L1 P1 ->
      DLJ_provable_sensible L1 (PPdisj P1 P2)
  | DLJ_disj_succedent_r_sensible P1 P2 L1 :
      DLJ_provable L1 P2 ->
      DLJ_provable_sensible L1 (PPdisj P1 P2).


Ltac DLJ_sensible_reorder_antecedent L :=
  apply (DLJ_perm_sensible _ L); [perm|].

Instance DLJ_provable_sensible_compat :
  Proper (@Permutation _==>eq==>iff) DLJ_provable_sensible.
Proof.
unfold Proper,respectful.
intros L1 L2 HL P1 P2 HP.
split.
- intros H.
  rewrite <-HP.
  exact (DLJ_perm_sensible P1 L1 L2 HL H).
- intros H.
  rewrite ->HP.
  exact (DLJ_perm_sensible P2 L2 L1 (Permutation_sym HL) H).
Qed.

Lemma DLJ_irreducible_sensible:
  forall L1 P1,
    DLJ_provable L1 P1 ->
    DLJ_antecedent_irreducible L1 ->
    DLJ_provable_sensible L1 P1.
Proof.
intros L1 P1 HPr HIr.
induction HPr.
- rewrite <-H.
  apply IHHPr.
  rewrite H.
  exact HIr.
- apply DLJ_axiom_sensible.
- apply DLJ_exfalso_sensible.
- destruct P1 as [|A1|P1A P1B|P1A P1B|P1A P1B].
  + apply DLJ_impl_antecedent_sensible.
    * exists.
    * apply HPr1.
    * apply HPr2.
  + specialize (IHHPr1 HIr).
    clear IHHPr2.
    rename IHHPr1 into IHHPr.
    remember (PPimpl (PPatom A1) P2 :: L1) as L2 in IHHPr.
    remember (PPatom A1) as P4 in IHHPr.
    apply eq_then_Permutation in HeqL2.
    induction IHHPr.
    * apply IHIHHPr.
      {
        rewrite H.
        exact HeqL2.
      }
      exact HeqP4.
    * rewrite HeqP4 in HeqL2.
      apply PProp_perm_select in HeqL2.
      destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
      { congruence. }
      exfalso.
      rewrite PrC in HIr.
      apply (DLJ_irred_impl _ HIr A1 P2).
      {
        apply in_eq.
      }
      right.
      apply in_eq.
    * apply PProp_perm_select in HeqL2.
      destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
      { congruence. }
      exfalso.
      rewrite PrC in HIr.
      apply (DLJ_irred_bot _ HIr).
      right.
      apply in_eq.
    * {
        apply PProp_perm_select in HeqL2.
        destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
        - replace P1 with (PPatom A1) in H by congruence.
          contradict H.
        - rewrite PrC.
          rewrite perm_swap.
          apply DLJ_impl_antecedent_sensible.
          + exact H.
          + rewrite <-PrD.
            exact H0.
          + rewrite perm_swap.
            apply DLJ_impl_antecedent.
            * rewrite perm_swap.
              rewrite <-PrD.
              rewrite <-HeqP4.
              exact H1.
            * rewrite perm_swap.
              apply DLJ_impl_antecedent_weak with (P1:=P1).
              rewrite perm_swap.
              rewrite <-PrC.
              exact HPr2.
      }
    * congruence.
    * apply PProp_perm_select in HeqL2.
      destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
      { congruence. }
      exfalso.
      rewrite PrC in HIr.
      apply (DLJ_irred_conj _ HIr P1 P0).
      right.
      apply in_eq.
    * congruence.
    *apply PProp_perm_select in HeqL2.
      destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
      { congruence. }
      exfalso.
      rewrite PrC in HIr.
      apply (DLJ_irred_disj _ HIr P1 P0).
      right.
      apply in_eq.
    * congruence.
    * congruence.
  + apply DLJ_impl_antecedent_sensible.
    * exists.
    * apply HPr1.
    * apply HPr2.
  + apply DLJ_impl_antecedent_sensible.
    * exists.
    * apply HPr1.
    * apply HPr2.
  + apply DLJ_impl_antecedent_sensible.
    * exists.
    * apply HPr1.
    * apply HPr2.
- apply DLJ_impl_succedent_sensible.
  exact HPr.
- apply DLJ_conj_antecedent_sensible.
  exact HPr.
- apply DLJ_conj_succedent_sensible.
  + exact HPr1.
  + exact HPr2.
- apply DLJ_disj_antecedent_sensible.
  + exact HPr1.
  + exact HPr2.
- apply DLJ_disj_succedent_l_sensible.
  exact HPr.
- apply DLJ_disj_succedent_r_sensible.
  exact HPr.
Qed.

Lemma DLI_Lem2:
  forall P2 P3 P4 L1,
    DLJ_provable (PPimpl (PPimpl P3 P4) P2::L1) (PPimpl P3 P4) <->
    DLJ_provable (PPimpl P4 P2::L1) (PPimpl P3 P4).
Proof.
intros P2 P3 P4 L1.
split.
- intros H.
  apply DLJ_impl_succedent.
  apply DLJ_cut with (P1:=PPimpl (PPimpl P3 P4) P2).
  + apply DLJ_impl_succedent.
    DLJ_reorder_antecedent (PPimpl P4 P2::PPimpl P3 P4::P3::L1).
    apply DLJ_impl_antecedent.
    * apply DLJ_weak.
      apply DLJ_impl_antecedent.
      {
        apply DLJ_weak.
        apply DLJ_axiom.
      }
      apply DLJ_axiom.
    * apply DLJ_axiom.
  + DLJ_reorder_antecedent (PPimpl P4 P2::P3::PPimpl (PPimpl P3 P4) P2::L1).
    apply DLJ_weak.
    apply DLJ_impl_elim.
    exact H.
- intros H.
  apply DLJ_impl_succedent.
  apply DLJ_cut with (P1:=PPimpl P4 P2).
  + apply DLJ_impl_succedent.
    DLJ_reorder_antecedent (PPimpl (PPimpl P3 P4) P2::P4::P3::L1).
    apply DLJ_impl_antecedent.
    * apply DLJ_impl_succedent.
      do 2 apply DLJ_weak.
      apply DLJ_axiom.
    * apply DLJ_axiom.
  + DLJ_reorder_antecedent (PPimpl (PPimpl P3 P4) P2::P3::PPimpl P4 P2::L1).
    apply DLJ_weak.
    apply DLJ_impl_elim.
    exact H.
Qed.

Lemma DLI_provable_DLJ_provable:
  forall P1 L1, DLI_provable L1 P1 -> DLJ_provable L1 P1.
Proof.
intros P1 L1 H.
induction H.
- rewrite <-H.
  exact IHDLI_provable.
- apply DLJ_axiom.
- apply DLJ_exfalso.
- apply DLJ_impl_antecedent.
  + apply DLJ_weak.
    apply DLJ_axiom.
  + exact IHDLI_provable.
- apply DLJ_impl_antecedent.
  + rewrite DLI_Lem2.
    exact IHDLI_provable1.
  + exact IHDLI_provable2.
- apply DLJ_cut with (P1:=PPimpl P2 (PPimpl P3 P1)).
  + apply DLJ_impl_succedent.
    apply DLJ_impl_succedent.
    DLJ_reorder_antecedent (PPimpl (PPconj P2 P3) P1 :: P2 :: P3 :: L1).
    apply DLJ_impl_antecedent; [|apply DLJ_axiom].
    apply DLJ_weak.
    apply DLJ_conj_succedent.
    * apply DLJ_axiom.
    * apply DLJ_weak.
      apply DLJ_axiom.
  + rewrite perm_swap.
    apply DLJ_weak.
    exact IHDLI_provable.
- apply DLJ_cut with (P1:=PPimpl P2 P1).
  {
    apply DLJ_impl_succedent.
    rewrite perm_swap.
    apply DLJ_impl_antecedent; [|apply DLJ_axiom].
    apply DLJ_disj_succedent_l.
    apply DLJ_weak.
    apply DLJ_axiom.
  }
  apply DLJ_cut with (P1:=PPimpl P3 P1).
  {
    apply DLJ_weak.
    apply DLJ_impl_succedent.
    rewrite perm_swap.
    apply DLJ_impl_antecedent; [|apply DLJ_axiom].
    apply DLJ_disj_succedent_r.
    apply DLJ_weak.
    apply DLJ_axiom.
  }
  DLJ_reorder_antecedent
      (PPimpl (PPdisj P2 P3) P1::PPimpl P2 P1 :: PPimpl P3 P1::L1).
  apply DLJ_weak.
  exact IHDLI_provable.
- apply DLJ_impl_succedent.
  exact IHDLI_provable.
- apply DLJ_conj_antecedent.
  exact IHDLI_provable.
- apply DLJ_conj_succedent.
  + exact IHDLI_provable1.
  + exact IHDLI_provable2.
- apply DLJ_disj_antecedent.
  + exact IHDLI_provable1.
  + exact IHDLI_provable2.
- apply DLJ_disj_succedent_l.
  exact IHDLI_provable.
- apply DLJ_disj_succedent_r.
  exact IHDLI_provable.
Qed.


Inductive DLJ_irreducibility(L1:list PProp):Set :=
  | DLJ_red_bot: In PPbot L1 -> DLJ_irreducibility L1
  | DLJ_red_impl A1 P1:
      In (PPimpl (PPatom A1) P1) L1 -> In (PPatom A1) L1 -> DLJ_irreducibility L1
  | DLJ_red_conj P1 P2:
      In (PPconj P1 P2) L1 -> DLJ_irreducibility L1
  | DLJ_red_disj P1 P2:
      In (PPdisj P1 P2) L1 -> DLJ_irreducibility L1
  | DLJ_irred: DLJ_antecedent_irreducible L1 -> DLJ_irreducibility L1.

Lemma find_list:
  forall(A:Type) (P:A->Prop) (L:list A),
    (forall a, {P a}+{~P a}) ->
    { a | In a L /\ P a } + { forall a, In a L -> ~P a }.
Proof.
intros A P L P_dec.
induction L.
{
  right.
  intros a [].
}
destruct IHL as [(b,(HbA,HbB))|IHL].
- left.
  exists b.
  split.
  + right.
    exact HbA.
  + exact HbB.
- destruct (P_dec a) as [Ha|Ha].
  + left.
    exists a.
    split.
    * apply in_eq.
    * exact Ha.
  + right.
    intros b [Hb|Hb].
    * rewrite <-Hb.
      exact Ha.
    * apply IHL.
      exact Hb.
Qed.

Lemma DLJ_irreducibility_dec: forall L1, DLJ_irreducibility L1.
Proof.
intros L1.
destruct (
    find_list _ (fun a =>
      match a with
      | PPbot => True
      | PPimpl (PPatom b) _ => In (PPatom b) L1
      | PPconj _ _ => True
      | PPdisj _ _ => True
      | _ => False
      end
    ) L1) as [(a,(HaA,HaB))|H1].
{
  intros a.
  destruct a as [|A1|[|A1|P1 P2|P1 P2|P1 P2] P3|P1 P2|P1 P2].
  - left; exists.
  - right; tauto.
  - right; tauto.
  - apply in_dec.
    apply PProp_dec.
  - right; tauto.
  - right; tauto.
  - right; tauto.
  - left; exists.
  - left; exists.
}
{
  destruct a as [|A1|[|A1|P1 P2|P1 P2|P1 P2] P3|P1 P2|P1 P2].
  - apply DLJ_red_bot.
    exact HaA.
  - contradict HaB.
  - contradict HaB.
  - apply DLJ_red_impl with (A1:=A1) (P1:=P3).
    + exact HaA.
    + exact HaB.
  - contradict HaB.
  - contradict HaB.
  - contradict HaB.
  - apply DLJ_red_conj with (P1:=P1) (P2:=P2).
    exact HaA.
  - apply DLJ_red_disj with (P1:=P1) (P2:=P2).
    exact HaA.
}
apply DLJ_irred.
split.
- intros H.
  exact (H1 _ H I).
- intros A1 P1 HA HB.
  exact (H1 _ HA HB).
- intros P1 P2 H.
  exact (H1 _ H I).
- intros P1 P2 H.
  exact (H1 _ H I).
Qed.

Fixpoint DLI_prop_weight(P:PProp):nat :=
  match P with
  | PPbot => 1
  | PPatom n => 1
  | PPimpl P1 P2 => 1 + DLI_prop_weight P1 + DLI_prop_weight P2
  | PPconj P1 P2 => 2 + DLI_prop_weight P1 + DLI_prop_weight P2
  | PPdisj P1 P2 => 1 + DLI_prop_weight P1 + DLI_prop_weight P2
  end.

Lemma DLJ_provable_DLI_provable:
  forall P1 L1, DLJ_provable L1 P1 -> DLI_provable L1 P1.
Proof.
intros P1 L1 H.
remember (P1::L1) as L2.
apply eq_then_Permutation in HeqL2.
revert P1 L1 HeqL2 H.
induction L2 as (L2,IHL2) using
    (well_founded_ind
      (multiset_ordering_wf _ _
        (well_founded_ltof _ DLI_prop_weight))).
intros P1 L1 HeqL2 H.
destruct (DLJ_irreducibility_dec L1) as
    [HIr|A1 P2 HIrA HIrB|P2 P3 HIr|P2 P3 HIr|HIr].
- apply in_split in HIr.
  destruct HIr as (L1A,(L1B,HL1)).
  rewrite HL1.
  DLI_reorder_antecedent (PPbot::L1A++L1B).
  apply DLI_exfalso.
- apply in_split in HIrA.
  destruct HIrA as (L1A,(L1B,HL1)).
  apply eq_then_Permutation in HL1.
  setoid_replace (L1A++PPimpl (PPatom A1) P2::L1B)
      with       (PPimpl (PPatom A1) P2::L1A++L1B)
      using relation (@Permutation PProp) in HL1; [|perm].
  rewrite HL1 in * |- *.
  clear L1 HL1.
  remember (L1A ++ L1B) as L1X.
  clear L1A L1B HeqL1X.
  destruct HIrB as [HIrB|HIrB].
  { congruence. }
  apply in_split in HIrB.
  destruct HIrB as (L1XA,(L1XB,HL1X)).
  apply eq_then_Permutation in HL1X.
  setoid_replace (L1XA++PPatom A1::L1XB)
      with       (PPatom A1::L1XA++L1XB)
      using relation (@Permutation PProp) in HL1X; [|perm].
  rewrite HL1X in * |- *.
  clear L1X HL1X.
  remember (L1XA ++ L1XB) as L1Y.
  clear L1XA L1XB HeqL1Y.
  apply DLI_impl_antecedent_atom.
  apply IHL2 with (y:=P1::P2::PPatom A1::L1Y).
  + rewrite HeqL2.
    exists (P1::PPatom A1::L1Y),(P2::nil),(PPimpl (PPatom A1) P2::nil).
    split.
    { split; perm. }
    split.
    { congruence. }
    intros P0 [HP0|[]].
    rewrite <-HP0.
    clear P0 HP0.
    exists (PPimpl (PPatom A1) P2).
    split.
    { apply in_eq. }
    unfold ltof.
    simpl.
    omega.
  + reflexivity.
  + apply DLJ_impl_antecedent_weak with (P1:=PPatom A1).
    exact H.
- apply in_split in HIr.
  destruct HIr as (L1A,(L1B,HL1)).
  apply eq_then_Permutation in HL1.
  setoid_replace (L1A++PPconj P2 P3::L1B)
      with       (PPconj P2 P3::L1A++L1B)
      using relation (@Permutation PProp) in HL1; [|perm].
  rewrite HL1 in * |- *.
  clear L1 HL1.
  remember (L1A++L1B) as L1X.
  clear L1A L1B HeqL1X.
  apply DLI_conj_antecedent.
  apply IHL2 with (y:=P1::P2::P3::L1X).
  + rewrite HeqL2.
    exists (P1::L1X),(P2::P3::nil),(PPconj P2 P3::nil).
    split.
    { split; perm. }
    split.
    { congruence. }
    intros P0 [HP0|[HP0|[]]].
    * rewrite <-HP0.
      clear P0 HP0.
      exists (PPconj P2 P3).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    * rewrite <-HP0.
      clear P0 HP0.
      exists (PPconj P2 P3).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
  + reflexivity.
  + apply DLJ_conj_elimL.
    exact H.
- apply in_split in HIr.
  destruct HIr as (L1A,(L1B,HL1)).
  apply eq_then_Permutation in HL1.
  setoid_replace (L1A++PPdisj P2 P3::L1B)
      with       (PPdisj P2 P3::L1A++L1B)
      using relation (@Permutation PProp) in HL1; [|perm].
  rewrite HL1 in * |- *.
  clear L1 HL1.
  remember (L1A++L1B) as L1X.
  clear L1A L1B HeqL1X.
  apply DLI_disj_antecedent.
  + apply IHL2 with (y:=P1::P2::L1X).
    * rewrite HeqL2.
      exists (P1::L1X),(P2::nil),(PPdisj P2 P3::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0.
      clear P0 HP0.
      exists (PPdisj P2 P3).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    * reflexivity.
    * apply DLJ_disj_elimL_l with (P2:=P3).
      exact H.
  + apply IHL2 with (y:=P1::P3::L1X).
    * rewrite HeqL2.
      exists (P1::L1X),(P3::nil),(PPdisj P2 P3::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0.
      clear P0 HP0.
      exists (PPdisj P2 P3).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    * reflexivity.
    * apply DLJ_disj_elimL_r with (P1:=P2).
      exact H.
- assert (HS := DLJ_irreducible_sensible _ _ H HIr).
  clear H HIr.
  induction HS.
  + rewrite <-H.
    apply IHHS.
    rewrite H.
    exact HeqL2.
  + apply DLI_axiom.
  + apply DLI_exfalso.
  + destruct P1 as [|A1|P4 P5|P4 P5|P4 P5].
    * {
        apply DLI_weak.
        apply IHL2 with (y:=P3::L1).
        - rewrite HeqL2.
          exists (P3::L1),nil,(PPimpl PPbot P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [].
        - reflexivity.
        - apply DLJ_cut with (P1 := PPimpl PPbot P2).
          + apply DLJ_impl_succedent.
            apply DLJ_exfalso.
          + revert H0.
            do 2 rewrite <-LJ_DLJ_iff.
            apply LJ.LJ_bot_elim.
      }
    * contradict H.
    * {
        apply DLI_impl_antecedent_impl.
        - apply DLI_impl_succedent.
          apply IHL2 with (y:=P5::P4::PPimpl P5 P2::L1).
          + rewrite HeqL2.
            exists L1,(P5::P4::PPimpl P5 P2::nil),
                (P3::PPimpl (PPimpl P4 P5) P2::nil).
            split.
            { split; perm. }
            split.
            { congruence. }
            intros P0 [HP0|[HP0|[HP0|[]]]].
            * rewrite <-HP0.
              clear P0 HP0.
              exists (PPimpl (PPimpl P4 P5) P2).
              split.
              { right; apply in_eq. }
              unfold ltof.
              simpl.
              omega.
            * rewrite <-HP0.
              clear P0 HP0.
              exists (PPimpl (PPimpl P4 P5) P2).
              split.
              { right; apply in_eq. }
              unfold ltof.
              simpl.
              omega.
            * rewrite <-HP0.
              clear P0 HP0.
              exists (PPimpl (PPimpl P4 P5) P2).
              split.
              { right; apply in_eq. }
              unfold ltof.
              simpl.
              omega.
          + reflexivity.
          + apply DLJ_impl_elim.
            rewrite <-DLI_Lem2.
            exact H0.
        - apply IHL2 with (y:=P3::P2::L1).
          + rewrite HeqL2.
            exists (P3::L1),(P2::nil),(PPimpl (PPimpl P4 P5) P2::nil).
            split.
            { split; perm. }
            split.
            { congruence. }
            intros P0 [HP0|[]].
            rewrite <-HP0.
            clear P0 HP0.
            exists (PPimpl (PPimpl P4 P5) P2).
            split.
            { apply in_eq. }
            unfold ltof.
            simpl.
            omega.
          + reflexivity.
          + exact H1.
      }
    * {
        apply DLI_impl_antecedent_conj.
        apply IHL2 with (y:=P3::PPimpl P4 (PPimpl P5 P2)::L1).
        - rewrite HeqL2.
          exists (P3::L1),(PPimpl P4 (PPimpl P5 P2)::nil),
              (PPimpl (PPconj P4 P5) P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0.
          clear P0 HP0.
          exists (PPimpl (PPconj P4 P5) P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - reflexivity.
        - apply DLJ_cut with (P1 := PPimpl (PPconj P4 P5) P2).
          {
            apply DLJ_impl_succedent.
            rewrite perm_swap.
            apply DLJ_impl_antecedent.
            {
              apply DLJ_weak.
              apply DLJ_conj_antecedent.
              apply DLJ_axiom.
            }
            apply DLJ_impl_antecedent.
            {
              apply DLJ_weak.
              apply DLJ_conj_antecedent.
              apply DLJ_weak.
              apply DLJ_axiom.
            }
            apply DLJ_axiom.
          }
          rewrite perm_swap.
          apply DLJ_weak.
          apply DLJ_impl_antecedent.
          + exact H0.
          + exact H1.
      }
    * {
        apply DLI_impl_antecedent_disj.
        apply IHL2 with (y:=P3::PPimpl P4 P2::PPimpl P5 P2::L1).
        - rewrite HeqL2.
          exists (P3::L1),(PPimpl P4 P2::PPimpl P5 P2::nil),
              (PPimpl (PPdisj P4 P5) P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[HP0|[]]].
          + rewrite <-HP0.
            clear P0 HP0.
            exists (PPimpl (PPdisj P4 P5) P2).
            split.
            { apply in_eq. }
            unfold ltof.
            simpl.
            omega.
          + rewrite <-HP0.
            clear P0 HP0.
            exists (PPimpl (PPdisj P4 P5) P2).
            split.
            { apply in_eq. }
            unfold ltof.
            simpl.
            omega.
        - reflexivity.
        - apply DLJ_cut with (P1:=PPimpl (PPdisj P4 P5) P2).
          {
            apply DLJ_impl_succedent.
            apply DLJ_disj_antecedent.
            - apply DLJ_impl_elim.
              apply DLJ_axiom.
            - apply DLJ_impl_elim.
              apply DLJ_weak.
              apply DLJ_axiom.
          }
          DLJ_reorder_antecedent (
              PPimpl P4 P2::PPimpl P5 P2::PPimpl (PPdisj P4 P5) P2::L1).
          apply DLJ_weak.
          apply DLJ_weak.
          apply DLJ_impl_antecedent.
          + exact H0.
          + exact H1.
      }
  + apply DLI_impl_succedent.
    apply IHL2 with (y:=P2::P1::L1).
    * {
        rewrite HeqL2.
        exists L1,(P2::P1::nil),(PPimpl P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[HP0|[]]].
        - rewrite <-HP0.
          clear P0 HP0.
          exists (PPimpl P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - rewrite <-HP0.
          clear P0 HP0.
          exists (PPimpl P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
      }
    * reflexivity.
    * exact H.
  + apply DLI_conj_antecedent.
    apply IHL2 with (y:=P3::P1::P2::L1).
    * {
        rewrite HeqL2.
        exists (P3::L1),(P1::P2::nil),(PPconj P1 P2::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[HP0|[]]].
        - rewrite <-HP0.
          clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - rewrite <-HP0.
          clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
      }
    * reflexivity.
    * exact H.
  + apply DLI_conj_succedent.
    * {
        apply IHL2 with (y:=P1::L1).
        - rewrite HeqL2.
          exists L1,(P1::nil),(PPconj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0.
          clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - reflexivity.
        - exact H.
      }
    * {
        apply IHL2 with (y:=P2::L1).
        - rewrite HeqL2.
          exists L1,(P2::nil),(PPconj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0.
          clear P0 HP0.
          exists (PPconj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - reflexivity.
        - exact H0.
      }
  + apply DLI_disj_antecedent.
    * {
        apply IHL2 with (y:=P3::P1::L1).
        - rewrite HeqL2.
          exists (P3::L1),(P1::nil),(PPdisj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0.
          clear P0 HP0.
          exists (PPdisj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - reflexivity.
        - exact H.
      }
    * {
        apply IHL2 with (y:=P3::P2::L1).
        - rewrite HeqL2.
          exists (P3::L1),(P2::nil),(PPdisj P1 P2::nil).
          split.
          { split; perm. }
          split.
          { congruence. }
          intros P0 [HP0|[]].
          rewrite <-HP0.
          clear P0 HP0.
          exists (PPdisj P1 P2).
          split.
          { apply in_eq. }
          unfold ltof.
          simpl.
          omega.
        - reflexivity.
        - exact H0.
      }
  + apply DLI_disj_succedent_l.
    apply IHL2 with (y:=P1::L1).
    * rewrite HeqL2.
      exists L1,(P1::nil),(PPdisj P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0.
      clear P0 HP0.
      exists (PPdisj P1 P2).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    * reflexivity.
    * exact H.
  + apply DLI_disj_succedent_r.
    apply IHL2 with (y:=P2::L1).
    * rewrite HeqL2.
      exists L1,(P2::nil),(PPdisj P1 P2::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0.
      clear P0 HP0.
      exists (PPdisj P1 P2).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    * reflexivity.
    * exact H.
Qed.

Lemma DLJ_DLI_iff:
  forall P1 L1, DLJ_provable L1 P1 <-> DLI_provable L1 P1.
Proof.
intros P1 L1.
split.
- apply DLJ_provable_DLI_provable.
- apply DLI_provable_DLJ_provable.
Qed.

Lemma find_list2:
  forall(A:Type) (P:A->Prop) (L:list A),
    (forall a, In a L -> {P a}+{~P a}) ->
    { a | In a L /\ P a } + { forall a, In a L -> ~P a }.
Proof.
intros A P L P_dec.
induction L.
{
  right.
  intros a [].
}
destruct IHL as [(b,(HbA,HbB))|IHL].
- intros b Hb.
  apply P_dec.
  right.
  exact Hb.
- left.
  exists b.
  split.
  + right.
    exact HbA.
  + exact HbB.
- destruct (P_dec a) as [Ha|Ha].
  + apply in_eq.
  + left.
    exists a.
    split.
    * apply in_eq.
    * exact Ha.
  + right.
    intros b [Hb|Hb].
    * rewrite <-Hb.
      exact Ha.
    * apply IHL.
      exact Hb.
Qed.

Lemma PProp_in_get:
  forall(P1:PProp) (L1:list PProp), In P1 L1 -> { L2 | Permutation L1 (P1::L2) }.
Proof.
intros P1 L1.
induction L1.
{ intros []. }
destruct (PProp_dec P1 a) as [HP1e|HP1n].
- intros _.
  exists L1.
  rewrite HP1e.
  reflexivity.
- intros H.
  destruct IHL1 as (L2,HL2).
  {
    destruct H as [H|H].
    - congruence.
    - exact H.
  }
  exists (a::L2).
  rewrite HL2.
  apply perm_swap.
Qed.

Fixpoint PProp_list_remove(P1:PProp) (L1:list PProp):list PProp :=
  match L1 with
  | nil => nil
  | L1h :: L1T =>
      if PProp_dec P1 L1h then
        L1T
      else
        L1h :: PProp_list_remove P1 L1T
  end.

Lemma PProp_list_remove_cons:
  forall P1 L1, PProp_list_remove P1 (P1::L1) = L1.
Proof.
intros P1 L1.
simpl.
destruct (PProp_dec P1 P1) as [|Hneq].
- reflexivity.
- congruence.
Qed.

Lemma PProp_list_remove_in:
  forall P1 L1, In P1 L1 -> Permutation L1 (P1::PProp_list_remove P1 L1).
Proof.
intros P1 L1.
induction L1.
{ intros []. }
unfold PProp_list_remove.
destruct (PProp_dec P1 a) as [Heq|Hneq].
- rewrite <-Heq.
  intros _.
  reflexivity.
- intros [H|H].
  { congruence. }
  rewrite perm_swap.
  apply Permutation_cons.
  apply IHL1.
  apply H.
Qed.

Instance PProp_list_remove_compat:
  Proper (eq ==> @Permutation PProp ==> @Permutation PProp) PProp_list_remove.
Proof.
unfold Proper,respectful.
intros P1 P HP.
rewrite HP; clear P1 HP.
intros L1 L2 HL.
induction HL.
- reflexivity.
- simpl.
  destruct (PProp_dec P x).
  + exact HL.
  + apply Permutation_cons.
    exact IHHL.
- simpl.
  destruct (PProp_dec P x) as [HXeq|HXneq];
  destruct (PProp_dec P y) as [HYeq|HYneq].
  + rewrite <-HXeq,<-HYeq.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + apply perm_swap.
- rewrite IHHL1,IHHL2.
  reflexivity.
Qed.

Lemma DLI_dec:
  forall P1 L1, {DLI_provable L1 P1} + {~DLI_provable L1 P1}.
Proof.
intros P1 L1.
remember (P1::L1) as L2.
revert P1 L1 HeqL2.
induction L2 as (L2,IHL2) using
    (well_founded_induction
      (multiset_ordering_wf _ _
        (well_founded_ltof _ DLI_prop_weight))).
intros P1 L1 HeqL2.
rewrite HeqL2 in IHL2.
clear L2 HeqL2.
assert (IH:
  forall P1' L1', 
    multiset_ordering PProp (ltof PProp DLI_prop_weight) (P1'::L1') (P1::L1) ->
    {DLI_provable L1' P1'} + {~DLI_provable L1' P1'}).
{
  intros P1' L1' H.
  apply (IHL2 (P1'::L1') H).
  reflexivity.
}
clear IHL2.

destruct (in_dec PProp_dec P1 L1) as [axiom_exist|axiom_nonexist].
{
  left.
  apply PProp_in_get in axiom_exist.
  destruct axiom_exist as (L1X,HL1X).
  rewrite HL1X.
  apply DLI_axiom.
}

destruct (
    find_list2 _ (fun a =>
      match a with
      | PPbot => True
      | PPimpl (PPatom b) PA => In (PPatom b) L1 /\
            DLI_provable (PA::PPatom b::
              PProp_list_remove (PPatom b) (
                PProp_list_remove (PPimpl (PPatom b) PA) L1
              )
            ) P1
      | PPimpl (PPimpl PB PC) PA =>
            DLI_provable (PPimpl PC PA::
              PProp_list_remove (PPimpl (PPimpl PB PC) PA) L1
            ) (PPimpl PB PC) /\
            DLI_provable (PA::
              PProp_list_remove (PPimpl (PPimpl PB PC) PA) L1
            ) P1
      | PPimpl (PPconj PB PC) PA =>
            DLI_provable (PPimpl PB (PPimpl PC PA)::
              PProp_list_remove (PPimpl (PPconj PB PC) PA) L1
            ) P1
      | PPimpl (PPdisj PB PC) PA =>
            DLI_provable (PPimpl PB PA::PPimpl PC PA::
              PProp_list_remove (PPimpl (PPdisj PB PC) PA) L1
            ) P1
      | PPconj PA PB =>
            DLI_provable (PA::PB::
              PProp_list_remove (PPconj PA PB) L1
            ) P1
      | PPdisj PA PB =>
            DLI_provable (PA::
              PProp_list_remove (PPdisj PA PB) L1
            ) P1 /\
            DLI_provable (PB::
              PProp_list_remove (PPdisj PA PB) L1
            ) P1
      | _ => False
      end
    ) L1) as [(a,(HaA,HaB))|antecedent_nonexist].
{
  intros a Ha.
  destruct a as [|A1|[|A1|P2 P3|P2 P3|P2 P3] P4|P2 P3|P2 P3].
  - left; exists.
  - right; tauto.
  - right; tauto.
  - destruct (in_dec PProp_dec (PPatom A1)
      (PProp_list_remove (PPimpl (PPatom A1) P4) L1)) as [Hin|Hnin].
    + destruct (IH P1 (P4::PPatom A1::
        PProp_list_remove (PPatom A1)
          (PProp_list_remove (PPimpl (PPatom A1) P4) L1))) as [HPr|HPrN].
      {
        rewrite <-(PProp_list_remove_in _ _ Hin).
        rewrite (PProp_list_remove_in _ _ Ha) at 2.
        exists (P1::PProp_list_remove (PPimpl (PPatom A1) P4) L1),
            (P4::nil),(PPimpl (PPatom A1) P4::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPatom A1) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      }
      * left.
        split.
        {
          rewrite (PProp_list_remove_in _ _ Ha).
          right.
          exact Hin.
        }
        exact HPr.
      * right.
        intros (_,HB).
        contradict HPrN.
        exact HB.
    + right.
      intros (HA,_).
      contradict Hnin.
      rewrite (PProp_list_remove_in _ _ Ha) in HA.
      destruct HA as [HA|HA].
      * congruence.
      * exact HA.
  - destruct (IH (PPimpl P2 P3) (PPimpl P3 P4::
        PProp_list_remove (PPimpl (PPimpl P2 P3) P4) L1)) as [HPrA|HPrNA].
    {
      rewrite (PProp_list_remove_in _ _ Ha) at 2.
      exists (PProp_list_remove (PPimpl (PPimpl P2 P3) P4) L1),
          (PPimpl P2 P3::PPimpl P3 P4::nil),(PPimpl (PPimpl P2 P3) P4::P1::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[HP0|[]]].
      - rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPimpl P2 P3) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      - rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPimpl P2 P3) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
    }
    + destruct (IH P1 (P4::
          PProp_list_remove (PPimpl (PPimpl P2 P3) P4) L1)) as [HPrB|HPrNB].
      {
        rewrite (PProp_list_remove_in _ _ Ha) at 2.
        exists (P1::PProp_list_remove (PPimpl (PPimpl P2 P3) P4) L1),
            (P4::nil),(PPimpl (PPimpl P2 P3) P4::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPimpl P2 P3) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      }
      * left.
        exact (conj HPrA HPrB).
      * right.
        intros (_,HPrB).
        contradict HPrNB.
        exact HPrB.
    + right.
      intros (HPrA,_).
      contradict HPrNA.
      exact HPrA.
  - destruct (IH P1 (PPimpl P2 (PPimpl P3 P4)::
        PProp_list_remove (PPimpl (PPconj P2 P3) P4) L1)) as [HPr|HPrN].
    {
      rewrite (PProp_list_remove_in _ _ Ha) at 2.
      exists (P1::PProp_list_remove (PPimpl (PPconj P2 P3) P4) L1),
          (PPimpl P2 (PPimpl P3 P4)::nil),(PPimpl (PPconj P2 P3) P4::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0; clear P0 HP0.
      exists (PPimpl (PPconj P2 P3) P4).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    }
    + left.
      exact HPr.
    + right.
      exact HPrN.
  - destruct (IH P1 (PPimpl P2 P4::PPimpl P3 P4::
        PProp_list_remove (PPimpl (PPdisj P2 P3) P4) L1)) as [HPr|HPrN].
    {
      rewrite (PProp_list_remove_in _ _ Ha) at 2.
      exists (P1::PProp_list_remove (PPimpl (PPdisj P2 P3) P4) L1),
          (PPimpl P2 P4::PPimpl P3 P4::nil),(PPimpl (PPdisj P2 P3) P4::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[HP0|[]]].
      - rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPdisj P2 P3) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      - rewrite <-HP0; clear P0 HP0.
        exists (PPimpl (PPdisj P2 P3) P4).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
    }
    + left.
      exact HPr.
    + right.
      exact HPrN.
  - destruct (IH P1 (P2::P3::
        PProp_list_remove (PPconj P2 P3) L1)) as [HPr|HPrN].
    {
      rewrite (PProp_list_remove_in _ _ Ha) at 2.
      exists (P1::PProp_list_remove (PPconj P2 P3) L1),
          (P2::P3::nil),(PPconj P2 P3::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[HP0|[]]].
      - rewrite <-HP0; clear P0 HP0.
        exists (PPconj P2 P3).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      - rewrite <-HP0; clear P0 HP0.
        exists (PPconj P2 P3).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
    }
    + left.
      exact HPr.
    + right.
      exact HPrN.
  - destruct (IH P1 (P2::
        PProp_list_remove (PPdisj P2 P3) L1)) as [HPrA|HPrNA].
    {
      rewrite (PProp_list_remove_in _ _ Ha) at 2.
      exists (P1::PProp_list_remove (PPdisj P2 P3) L1),
          (P2::nil),(PPdisj P2 P3::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0; clear P0 HP0.
      exists (PPdisj P2 P3).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    }
    + destruct (IH P1 (P3::
          PProp_list_remove (PPdisj P2 P3) L1)) as [HPrB|HPrNB].
      {
        rewrite (PProp_list_remove_in _ _ Ha) at 2.
        exists (P1::PProp_list_remove (PPdisj P2 P3) L1),
            (P3::nil),(PPdisj P2 P3::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P2 P3).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      }
      * left.
        exact (conj HPrA HPrB).
      * right.
        intros (_,HPrB).
        contradict HPrNB.
        exact HPrB.
    + right.
      intros (HPrA,_).
      contradict HPrNA.
      exact HPrA.
}
{
  left.
  destruct a as [|A1|[|A1|P2 P3|P2 P3|P2 P3] P4|P2 P3|P2 P3].
  - rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_exfalso.
  - contradict HaB.
  - contradict HaB.
  - destruct HaB as (HaBA,HaBB).
    rewrite (PProp_list_remove_in _ _ HaA).
    rewrite (PProp_list_remove_in _ _ HaA) in HaBA.
    destruct HaBA as [HaBA|HaBA].
    { congruence. }
    rewrite (PProp_list_remove_in _ _ HaBA).
    apply DLI_impl_antecedent_atom.
    exact HaBB.
  - destruct HaB as (HaBA,HaBB).
    rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_impl_antecedent_impl.
    + exact HaBA.
    + exact HaBB.
  - rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_impl_antecedent_conj.
    exact HaB.
  - rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_impl_antecedent_disj.
    exact HaB.
  - rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_conj_antecedent.
    exact HaB.
  - destruct HaB as (HaBA,HaBB).
    rewrite (PProp_list_remove_in _ _ HaA).
    apply DLI_disj_antecedent.
    + exact HaBA.
    + exact HaBB.
}
assert (succedent_dec:
  {
    match P1 with
    | PPimpl P1A P1B => DLI_provable (P1A::L1) P1B
    | PPconj P1A P1B => DLI_provable L1 P1A /\ DLI_provable L1 P1B
    | PPdisj P1A P1B => DLI_provable L1 P1A \/ DLI_provable L1 P1B
    | _ => False
    end
  } + {~
    match P1 with
    | PPimpl P1A P1B => DLI_provable (P1A::L1) P1B
    | PPconj P1A P1B => DLI_provable L1 P1A /\ DLI_provable L1 P1B
    | PPdisj P1A P1B => DLI_provable L1 P1A \/ DLI_provable L1 P1B
    | _ => False
    end
  }).
{
  destruct P1 as [|A1|P1A P1B|P1A P1B|P1A P1B].
  - right; tauto.
  - right; tauto.
  - apply IH.
    exists L1,(P1B::P1A::nil),(PPimpl P1A P1B::nil).
    split.
    { split; perm. }
    split.
    { congruence. }
    intros P0 [HP0|[HP0|[]]].
    + rewrite <-HP0; clear P0 HP0.
      exists (PPimpl P1A P1B).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    + rewrite <-HP0; clear P0 HP0.
      exists (PPimpl P1A P1B).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
  - destruct (IH P1A L1) as [HPrA|HPrNA].
    {
      exists L1,(P1A::nil),(PPconj P1A P1B::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0; clear P0 HP0.
      exists (PPconj P1A P1B).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    }
    + destruct (IH P1B L1) as [HPrB|HPrNB].
      {
        exists L1,(P1B::nil),(PPconj P1A P1B::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPconj P1A P1B).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      }
      * left.
        exact (conj HPrA HPrB).
      * right.
        intros (_,HPrB).
        apply HPrNB,HPrB.
    + right.
      intros (HPrA,_).
      apply HPrNA,HPrA.
  - destruct (IH P1A L1) as [HPrA|HPrNA].
    {
      exists L1,(P1A::nil),(PPdisj P1A P1B::nil).
      split.
      { split; perm. }
      split.
      { congruence. }
      intros P0 [HP0|[]].
      rewrite <-HP0; clear P0 HP0.
      exists (PPdisj P1A P1B).
      split.
      { apply in_eq. }
      unfold ltof.
      simpl.
      omega.
    }
    + left.
      left.
      exact HPrA.
    + destruct (IH P1B L1) as [HPrB|HPrNB].
      {
        exists L1,(P1B::nil),(PPdisj P1A P1B::nil).
        split.
        { split; perm. }
        split.
        { congruence. }
        intros P0 [HP0|[]].
        rewrite <-HP0; clear P0 HP0.
        exists (PPdisj P1A P1B).
        split.
        { apply in_eq. }
        unfold ltof.
        simpl.
        omega.
      }
      * left.
        right.
        exact HPrB.
      * right.
        intros [HPrA|HPrB]; contradiction.
}
destruct succedent_dec as [succedent_exist|succedent_nonexist].
{
  left.
  destruct P1.
  - contradict succedent_exist.
  - contradict succedent_exist.
  - apply DLI_impl_succedent.
    exact succedent_exist.
  - destruct succedent_exist as (HPrL,HPrR).
    apply DLI_conj_succedent.
    + exact HPrL.
    + exact HPrR.
  - destruct succedent_exist as [HPr|HPr].
    + apply DLI_disj_succedent_l.
      exact HPr.
    + apply DLI_disj_succedent_r.
      exact HPr.
}
right.
intros HPr.
clear IH.
induction HPr as
    [ P1 L1 L2 HPerm HPr
    | P1 L1
    | P1 L1
    | A1 P1 P2 L1 HPr
    | P1 P2 P3 P4 L1 HPrL HPrR
    | P1 P2 P3 P4 L1 HPr
    | P1 P2 P3 P4 L1 HPr
    | P1 P2 L1 HPr
    | P1 P2 P3 L1 HPr
    | P1 P2 L1 HPrL HPrR
    | P1 P2 P3 L1 HPrL HPrR
    | P1 P2 L1 HPr
    | P1 P2 L1 HPr].
- apply IHHPr.
  + intros H.
    contradict axiom_nonexist.
    rewrite <-HPerm.
    exact H.
  + intros a HaA HaB.
    apply (antecedent_nonexist a).
    {
      rewrite <-HPerm.
      exact HaA.
    }
    destruct a as [|A1|[|A1|P2 P3|P2 P3|P2 P3] P4|P2 P3|P2 P3];
      (try rewrite <-HPerm; exact HaB).
  + intros H.
    contradict succedent_nonexist.
    destruct P1; (try rewrite <-HPerm; exact H).
- contradict axiom_nonexist.
  apply in_eq.
- apply (antecedent_nonexist _ (in_eq _ _)).
  exists.
- apply (antecedent_nonexist _ (in_eq _ _)).
  split.
  { right; apply in_eq. }
  rewrite PProp_list_remove_cons.
  rewrite PProp_list_remove_cons.
  exact HPr.
- apply (antecedent_nonexist _ (in_eq _ _)).
  split.
  + rewrite PProp_list_remove_cons.
    exact HPrL.
  + rewrite PProp_list_remove_cons.
    exact HPr1.
- apply (antecedent_nonexist _ (in_eq _ _)).
  rewrite PProp_list_remove_cons.
  exact HPr.
- apply (antecedent_nonexist _ (in_eq _ _)).
  rewrite PProp_list_remove_cons.
  exact HPr.
- apply succedent_nonexist.
  exact HPr.
- apply (antecedent_nonexist _ (in_eq _ _)).
  rewrite PProp_list_remove_cons.
  exact HPr.
- apply succedent_nonexist.
  exact (conj HPrL HPr1).
- apply (antecedent_nonexist _ (in_eq _ _)).
  rewrite PProp_list_remove_cons.
  exact (conj HPrL HPr1).
- apply succedent_nonexist.
  left.
  exact HPr.
- apply succedent_nonexist.
  right.
  exact HPr.
Qed.

Theorem LJ_dec:
  forall P1 L1, {LJ.LJ_provable L1 P1} + {~LJ.LJ_provable L1 P1}.
Proof.
intros P1 L1.
destruct (DLI_dec P1 L1) as [HPr|HPrN].
- left.
  rewrite LJ_DLJ_iff.
  rewrite DLJ_DLI_iff.
  exact HPr.
- right.
  rewrite LJ_DLJ_iff.
  rewrite DLJ_DLI_iff.
  exact HPrN.
Qed.
