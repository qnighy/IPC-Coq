Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
Require Import MyPermutations.
Require Import PProp.
Require Import LJ.

(* Dyckhoff's LJ *)
Inductive DLJ_provable : list PProp -> PProp -> Prop :=
  | DLJ_perm P1 L1 L2 :
      Permutation L1 L2 ->
      DLJ_provable L1 P1 ->
      DLJ_provable L2 P1
  | DLJ_axiom P1 L1 :
      DLJ_provable (P1::L1) P1
  | DLJ_exfalso P1 L1 :
      DLJ_provable (PPbot::L1) P1
  | DLJ_impl_antecedent P1 P2 P3 L1 :
      DLJ_provable (PPimpl P1 P2::L1) P1 ->
      DLJ_provable (P2::L1) P3 ->
      DLJ_provable (PPimpl P1 P2::L1) P3
  | DLJ_impl_succedent P1 P2 L1 :
      DLJ_provable (P1::L1) P2 ->
      DLJ_provable L1 (PPimpl P1 P2)
  | DLJ_conj_antecedent P1 P2 P3 L1 :
      DLJ_provable (P1::P2::L1) P3 ->
      DLJ_provable (PPconj P1 P2::L1) P3
  | DLJ_conj_succedent P1 P2 L1 :
      DLJ_provable L1 P1 ->
      DLJ_provable L1 P2 ->
      DLJ_provable L1 (PPconj P1 P2)
  | DLJ_disj_antecedent P1 P2 P3 L1 :
      DLJ_provable (P1::L1) P3 ->
      DLJ_provable (P2::L1) P3 ->
      DLJ_provable (PPdisj P1 P2::L1) P3
  | DLJ_disj_succedent_l P1 P2 L1 :
      DLJ_provable L1 P1 ->
      DLJ_provable L1 (PPdisj P1 P2)
  | DLJ_disj_succedent_r P1 P2 L1 :
      DLJ_provable L1 P2 ->
      DLJ_provable L1 (PPdisj P1 P2).

Ltac DLJ_reorder_antecedent L :=
  apply (DLJ_perm _ L); [perm|].

Instance DLJ_provable_compat : Proper (@Permutation _==>eq==>iff) DLJ_provable.
Proof.
unfold Proper,respectful.
intros L1 L2 HL P1 P2 HP.
split.
- intros H.
  rewrite <-HP.
  exact (DLJ_perm P1 L1 L2 HL H).
- intros H.
  rewrite ->HP.
  exact (DLJ_perm P2 L2 L1 (Permutation_sym HL) H).
Qed.

Lemma DLJ_weak: forall P1 P2 L1, DLJ_provable L1 P2 -> DLJ_provable (P1::L1) P2.
Proof.
intros P1 P2 L1 H.
remember L1 as L2 in H.
apply eq_then_Permutation in HeqL2.
revert P1 L1 HeqL2.
induction H.
- intros OP1 OL1 HeqL2.
  apply IHDLJ_provable.
  rewrite H,HeqL2; reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  rewrite perm_swap.
  apply DLJ_axiom.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  rewrite perm_swap.
  apply DLJ_exfalso.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  rewrite perm_swap.
  apply DLJ_impl_antecedent.
  + rewrite perm_swap.
    apply IHDLJ_provable1.
    reflexivity.
  + rewrite perm_swap.
    apply IHDLJ_provable2.
    reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  apply DLJ_impl_succedent.
  rewrite perm_swap.
  apply IHDLJ_provable.
  reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  rewrite perm_swap.
  apply DLJ_conj_antecedent.
  DLJ_reorder_antecedent (OP1::P1::P2::L1).
  apply IHDLJ_provable.
  reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1.
    reflexivity.
  + apply IHDLJ_provable2.
    reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  rewrite perm_swap.
  apply DLJ_disj_antecedent.
  + rewrite perm_swap.
    apply IHDLJ_provable1.
    reflexivity.
  + rewrite perm_swap.
    apply IHDLJ_provable2.
    reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable.
  reflexivity.
- intros OP1 OL1 HeqL2.
  rewrite <-HeqL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable.
  reflexivity.
Qed.

Lemma DLJ_conj_elimL:
  forall P1 P2 P3 L1,
    DLJ_provable (PPconj P1 P2::L1) P3 -> DLJ_provable (P1::P2::L1) P3.
Proof.
intros P1 P2 P3 L1 H.
remember (PPconj P1 P2::L1) as L2 in H.
apply eq_then_Permutation in HeqL2.
revert P1 P2 L1 HeqL2.
induction H.
- intros OP1 OP2 OL1 HeqL2.
  apply IHDLJ_provable.
  rewrite H,HeqL2; reflexivity.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + rewrite PrA.
    apply DLJ_conj_succedent.
    * apply DLJ_axiom.
    * rewrite perm_swap.
      apply DLJ_axiom.
  + rewrite PrC.
    DLJ_reorder_antecedent (P1::OP1::OP2::L2').
    apply DLJ_axiom.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPbot::OP1::OP2::L2').
    apply DLJ_exfalso.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPimpl P1 P2::OP1::OP2::L2').
    apply DLJ_impl_antecedent.
    * DLJ_reorder_antecedent (OP1::OP2::PPimpl P1 P2::L2').
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP1::OP2::P2::L2').
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_impl_succedent.
  DLJ_reorder_antecedent (OP1::OP2::P1::OL1).
  apply IHDLJ_provable.
  rewrite HeqL2; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + replace OP1 with P1 by congruence.
    replace OP2 with P2 by congruence.
    rewrite <-PrB.
    exact H.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPconj P1 P2::OP1::OP2::L2').
    apply DLJ_conj_antecedent.
    DLJ_reorder_antecedent (OP1::OP2::P1::P2::L2').
    apply IHDLJ_provable.
    rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1.
    exact HeqL2.
  + apply IHDLJ_provable2.
    exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPdisj P1 P2::OP1::OP2::L2').
    apply DLJ_disj_antecedent.
    * DLJ_reorder_antecedent (OP1::OP2::P1::L2').
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP1::OP2::P2::L2').
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable.
  exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable.
  exact HeqL2.
Qed.

Lemma DLJ_disj_elimL_l:
  forall P1 P2 P3 L1,
    DLJ_provable (PPdisj P1 P2::L1) P3 -> DLJ_provable (P1::L1) P3.
Proof.
intros P1 P2 P3 L1 H.
remember (PPdisj P1 P2::L1) as L2 in H.
apply eq_then_Permutation in HeqL2.
revert P1 P2 L1 HeqL2.
induction H.
- intros OP1 OP2 OL1 HeqL2.
  apply IHDLJ_provable with (P3:=OP2).
  rewrite H,HeqL2; reflexivity.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + rewrite PrA.
    apply DLJ_disj_succedent_l.
    apply DLJ_axiom.
  + rewrite PrC.
    DLJ_reorder_antecedent (P1::OP1::L2').
    apply DLJ_axiom.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPbot::OP1::L2').
    apply DLJ_exfalso.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPimpl P1 P2::OP1::L2').
    apply DLJ_impl_antecedent.
    * DLJ_reorder_antecedent (OP1::PPimpl P1 P2::L2').
      apply IHDLJ_provable1 with (P4:=OP2).
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP1::P2::L2').
      apply IHDLJ_provable2 with (P4:=OP2).
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_impl_succedent.
  DLJ_reorder_antecedent (OP1::P1::OL1).
  apply IHDLJ_provable with (P4:=OP2).
  rewrite HeqL2; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPconj P1 P2::OP1::L2').
    apply DLJ_conj_antecedent.
    DLJ_reorder_antecedent (OP1::P1::P2::L2').
    apply IHDLJ_provable with (P5:=OP2).
    rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1 with (P3:=OP2).
    exact HeqL2.
  + apply IHDLJ_provable2 with (P3:=OP2).
    exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + replace OP1 with P1 by congruence.
    rewrite <-PrB.
    exact H.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPdisj P1 P2::OP1::L2').
    apply DLJ_disj_antecedent.
    * DLJ_reorder_antecedent (OP1::P1::L2').
      apply IHDLJ_provable1 with (P4:=OP2).
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP1::P2::L2').
      apply IHDLJ_provable2 with (P4:=OP2).
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable with (P3:=OP2).
  exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable with (P3:=OP2).
  exact HeqL2.
Qed.

Lemma DLJ_disj_elimL_r:
  forall P1 P2 P3 L1,
    DLJ_provable (PPdisj P1 P2::L1) P3 -> DLJ_provable (P2::L1) P3.
Proof.
intros P1 P2 P3 L1 H.
remember (PPdisj P1 P2::L1) as L2 in H.
apply eq_then_Permutation in HeqL2.
revert P1 P2 L1 HeqL2.
induction H.
- intros OP1 OP2 OL1 HeqL2.
  apply IHDLJ_provable with (P2:=OP1).
  rewrite H,HeqL2; reflexivity.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + rewrite PrA.
    apply DLJ_disj_succedent_r.
    apply DLJ_axiom.
  + rewrite PrC.
    DLJ_reorder_antecedent (P1::OP2::L2').
    apply DLJ_axiom.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPbot::OP2::L2').
    apply DLJ_exfalso.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPimpl P1 P2::OP2::L2').
    apply DLJ_impl_antecedent.
    * DLJ_reorder_antecedent (OP2::PPimpl P1 P2::L2').
      apply IHDLJ_provable1 with (P3:=OP1).
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP2::P2::L2').
      apply IHDLJ_provable2 with (P1:=OP1).
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_impl_succedent.
  DLJ_reorder_antecedent (OP2::P1::OL1).
  apply IHDLJ_provable with (P3:=OP1).
  rewrite HeqL2; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPconj P1 P2::OP2::L2').
    apply DLJ_conj_antecedent.
    DLJ_reorder_antecedent (OP2::P1::P2::L2').
    apply IHDLJ_provable with (P4:=OP1).
    rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1 with (P2:=OP1).
    exact HeqL2.
  + apply IHDLJ_provable2 with (P1:=OP1).
    exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + replace OP2 with P2 by congruence.
    rewrite <-PrB.
    exact H0.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPdisj P1 P2::OP2::L2').
    apply DLJ_disj_antecedent.
    * DLJ_reorder_antecedent (OP2::P1::L2').
      apply IHDLJ_provable1 with (P2:=OP1).
      rewrite PrD; perm.
    * DLJ_reorder_antecedent (OP2::P2::L2').
      apply IHDLJ_provable2 with (P1:=OP1).
      rewrite PrD; perm.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable with (P2:=OP1).
  exact HeqL2.
- intros OP1 OP2 OL1 HeqL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable with (P1:=OP1).
  exact HeqL2.
Qed.

Lemma DLJ_impl_antecedent_weak:
  forall P1 P2 P3 L1,
    DLJ_provable (PPimpl P1 P2::L1) P3 ->
    DLJ_provable (P2::L1) P3.
Proof.
intros P1 P2 P3 L1 H.
remember (PPimpl P1 P2::L1) as L2 in H.
apply eq_then_Permutation in HeqL2.
revert L1 HeqL2.
induction H.
- intros OL1 HeqL2.
  apply IHDLJ_provable.
  rewrite H,HeqL2; reflexivity.
- intros OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + rewrite PrA.
    apply DLJ_impl_succedent.
    rewrite perm_swap.
    apply DLJ_axiom.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_axiom.
- intros OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_exfalso.
- intros OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + replace P2 with P3 by congruence.
    rewrite <-PrB.
    exact H0.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_impl_antecedent.
    * rewrite perm_swap.
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OL1 HeqL2.
  apply DLJ_impl_succedent.
  rewrite perm_swap.
  apply IHDLJ_provable.
  rewrite HeqL2; perm.
- intros OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_conj_antecedent.
    DLJ_reorder_antecedent (P2::P0::P3::L2').
    apply IHDLJ_provable.
    rewrite PrD; perm.
- intros OL1 HeqL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1.
    exact HeqL2.
  + apply IHDLJ_provable2.
    exact HeqL2.
- intros OL1 HeqL2.
  apply PProp_perm_select in HeqL2.
  destruct HeqL2 as [(PrA,PrB) | (L2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_disj_antecedent.
    * rewrite perm_swap.
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OL1 HeqL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable.
  exact HeqL2.
- intros OL1 HeqL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable.
  exact HeqL2.
Qed.

Lemma DLJ_contr_permselect:
  forall(P1 P2:PProp) (L1 L2:list PProp),
    Permutation (P1::L1) (P2::P2::L2) ->
      (
        P1 = P2 /\ Permutation L1 (P2::L2)
      ) \/ (
        exists L2',
          Permutation L2 (P1::L2') /\
          Permutation L1 (P2::P2::L2')
      ).
Proof.
intros P1 P2 L1 L2 HP.
assert (HI:=in_eq P1 L1).
rewrite HP in HI.
assert (HI2:In P1 (P2::L2)).
{
  destruct HI as [HI|[HI|HI]].
  - left; exact HI.
  - left; exact HI.
  - right; exact HI.
}
clear HI.
destruct HI2 as [HI|HI].
- left.
  split.
  + symmetry.
    exact HI.
  + rewrite <-HI in HP.
    apply Permutation_cons_inv in HP.
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

Lemma DLJ_contr:
  forall P1 P2 L1,
    DLJ_provable (P1::P1::L1) P2 -> DLJ_provable (P1::L1) P2.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 H.
remember (KP1::KP1::KL1) as KL2 in H.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros OL1 HeqKL2.
  apply IHDLJ_provable.
  rewrite H,HeqKL2; reflexivity.
- intros OL1 HeqKL2.
  apply DLJ_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLJ_axiom.
  + rewrite PrC.
    DLJ_reorder_antecedent (P1::KP1::KL2').
    apply DLJ_axiom.
- intros OL1 HeqKL2.
  apply DLJ_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    apply DLJ_exfalso.
  + rewrite PrC.
    DLJ_reorder_antecedent (PPbot::KP1::KL2').
    apply DLJ_exfalso.
- intros OL1 HeqKL2.
  apply DLJ_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLJ_impl_antecedent.
      - rewrite PrA.
        apply IHDLJ_provable1.
        rewrite PrB,<-PrA; reflexivity.
      - apply HI_rank.
        + apply (PPsmall_impl_r _ (eq_sym PrA)).
        + apply DLJ_impl_antecedent_weak with (P1:=P1).
          rewrite PrA.
          rewrite perm_swap.
          rewrite <-PrB.
          exact H0.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_impl_antecedent.
    * rewrite perm_swap.
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLJ_impl_succedent.
  rewrite perm_swap.
  apply IHDLJ_provable.
  rewrite HeqKL2; perm.
- intros OL1 HeqKL2.
  apply DLJ_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLJ_conj_antecedent.
      apply HI_rank.
      {
        apply (PPsmall_conj_l _ (eq_sym PrA)).
      }
      DLJ_reorder_antecedent (P2::P1::P1::OL1).
      apply HI_rank.
      {
        apply (PPsmall_conj_r _ (eq_sym PrA)).
      }
      DLJ_reorder_antecedent (P1::P2::P1::P2::OL1).
      apply DLJ_conj_elimL.
      rewrite PrA.
      DLJ_reorder_antecedent (P1::P2::KP1::OL1).
      rewrite <-PrB.
      exact H.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_conj_antecedent.
    DLJ_reorder_antecedent (KP1::P1::P2::KL2').
    apply IHDLJ_provable.
    rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLJ_conj_succedent.
  + apply IHDLJ_provable1.
    exact HeqKL2.
  + apply IHDLJ_provable2.
    exact HeqKL2.
- intros OL1 HeqKL2.
  apply DLJ_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLJ_disj_antecedent.
      - apply HI_rank.
        {
          apply (PPsmall_disj_l _ (eq_sym PrA)).
        }
        apply DLJ_disj_elimL_l with (P2:=P2).
        rewrite PrA.
        rewrite perm_swap.
        rewrite <-PrB.
        exact H.
      - apply HI_rank.
        {
          apply (PPsmall_disj_r _ (eq_sym PrA)).
        }
        apply DLJ_disj_elimL_r with (P1:=P1).
        rewrite PrA.
        rewrite perm_swap.
        rewrite <-PrB.
        exact H0.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLJ_disj_antecedent.
    * rewrite perm_swap.
      apply IHDLJ_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLJ_provable2.
      rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLJ_disj_succedent_l.
  apply IHDLJ_provable.
  exact HeqKL2.
- intros OL1 HeqKL2.
  apply DLJ_disj_succedent_r.
  apply IHDLJ_provable.
  exact HeqKL2.
Qed.

Lemma LJ_impl_antecedent2:
  forall P1 P2 P3 L1,
    LJ_provable (PPimpl P1 P2::L1) P1 ->
    LJ_provable (P2::L1) P3 ->
    LJ_provable (PPimpl P1 P2::L1) P3.
Proof.
intros P1 P2 P3 L1 HPrL HPrR.
apply LJ_contr.
apply LJ_impl_antecedent.
- exact HPrL.
- rewrite perm_swap.
  apply LJ_weak.
  exact HPrR.
Qed.

Lemma DLJ_provable_LJ_provable:
  forall P1 L1, DLJ_provable L1 P1 -> LJ_provable L1 P1.
Proof.
intros P1 L1 H.
induction H.
- rewrite <-H.
  exact IHDLJ_provable.
- LJ_reorder_antecedent (L1++P1::nil).
  apply LJ_weakN.
  apply LJ_axiom.
- LJ_reorder_antecedent (L1++PPbot::nil).
  apply LJ_weakN.
  apply LJ_exfalso.
- apply LJ_impl_antecedent2.
  + exact IHDLJ_provable1.
  + exact IHDLJ_provable2.
- apply LJ_impl_succedent.
  exact IHDLJ_provable.
- apply LJ_conj_antecedent.
  exact IHDLJ_provable.
- apply LJ_conj_succedent.
  + exact IHDLJ_provable1.
  + exact IHDLJ_provable2.
- apply LJ_disj_antecedent.
  + exact IHDLJ_provable1.
  + exact IHDLJ_provable2.
- apply LJ_disj_succedent_l.
  exact IHDLJ_provable.
- apply LJ_disj_succedent_r.
  exact IHDLJ_provable.
Qed.

Lemma LJ_provable_DLJ_provable:
  forall P1 L1, LJ_provable L1 P1 -> DLJ_provable L1 P1.
Proof.
intros P1 L1 H.
induction H.
- rewrite <-H.
  exact IHLJ_provable.
- apply DLJ_weak.
  exact IHLJ_provable.
- apply DLJ_contr.
  exact IHLJ_provable.
- apply DLJ_axiom.
- apply DLJ_exfalso.
- apply DLJ_impl_antecedent.
  + apply DLJ_weak.
    exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply DLJ_impl_succedent.
  exact IHLJ_provable.
- apply DLJ_conj_antecedent.
  exact IHLJ_provable.
- apply DLJ_conj_succedent.
  + exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply DLJ_disj_antecedent.
  + exact IHLJ_provable1.
  + exact IHLJ_provable2.
- apply DLJ_disj_succedent_l.
  exact IHLJ_provable.
- apply DLJ_disj_succedent_r.
  exact IHLJ_provable.
Qed.

Lemma LJ_DLJ_iff:
  forall P1 L1, LJ_provable L1 P1 <-> DLJ_provable L1 P1.
Proof.
intros P1 L1.
split.
- apply LJ_provable_DLJ_provable.
- apply DLJ_provable_LJ_provable.
Qed.

Definition DLJ_tauto:PProp -> Prop := DLJ_provable nil.

Lemma LJ_DLJ_tauto_iff:
  forall P1, LJ_tauto P1 <-> DLJ_tauto P1.
Proof.
intros P1.
apply LJ_DLJ_iff.
Qed.

