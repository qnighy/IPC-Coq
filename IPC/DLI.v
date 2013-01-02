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

Lemma DLI_conj_elimL:
  forall P1 P2 P3 L1,
    DLI_provable (PPconj P1 P2::L1) P3 ->
    DLI_provable (P1::P2::L1) P3.
Proof.
intros KP1 KP2 KP3 KL1 H.
remember (PPconj KP1 KP2::KL1) as KL2.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros KL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2.
  reflexivity.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLI_conj_succedent.
    * apply DLI_axiom.
    * rewrite perm_swap.
      apply DLI_axiom.
  + rewrite PrC.
    DLI_reorder_antecedent (P1 :: KP1 :: KP2 :: KL2').
    apply DLI_axiom.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLI_reorder_antecedent (PPbot :: KP1 :: KP2 :: KL2').
    apply DLI_exfalso.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  { congruence. }
  rewrite PrC.
  apply PProp_perm_select in PrD.
  destruct PrD as [(PrE,PrF) | (KL2'',(PrG,PrH))].
  { congruence. }
  rewrite PrG.
  DLI_reorder_antecedent (PPimpl (PPatom A1) P1 :: PPatom A1 :: KP1 :: KP2 :: KL2'').
  apply DLI_impl_antecedent_atom.
  DLI_reorder_antecedent (KP1::KP2::P1::PPatom A1::KL2'').
  apply IHDLI_provable.
  rewrite PrH; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLI_reorder_antecedent (PPimpl (PPimpl P2 P3) P1 :: KP1 :: KP2 :: KL2').
    apply DLI_impl_antecedent_impl.
    * DLI_reorder_antecedent (KP1 :: KP2 :: PPimpl P3 P1 :: KL2').
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * DLI_reorder_antecedent (KP1 :: KP2 :: P1 :: KL2').
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLI_reorder_antecedent (PPimpl (PPconj P2 P3) P1 :: KP1 :: KP2 :: KL2').
    apply DLI_impl_antecedent_conj.
    DLI_reorder_antecedent (KP1 :: KP2 :: PPimpl P2 (PPimpl P3 P1) :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLI_reorder_antecedent (PPimpl (PPdisj P2 P3) P1 :: KP1 :: KP2 :: KL2').
    apply DLI_impl_antecedent_disj.
    DLI_reorder_antecedent (KP1 :: KP2 :: PPimpl P2 P1 :: PPimpl P3 P1 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_impl_succedent.
  DLI_reorder_antecedent (KP1 :: KP2 :: P1 :: KL1).
  apply IHDLI_provable.
  rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP1 with P1 by congruence.
    replace KP2 with P2 by congruence.
    rewrite <-PrB.
    exact H.
  + rewrite PrC.
    DLI_reorder_antecedent (PPconj P1 P2 :: KP1 :: KP2 :: KL2').
    apply DLI_conj_antecedent.
    DLI_reorder_antecedent (KP1 :: KP2 :: P1 :: P2 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_conj_succedent.
  + apply IHDLI_provable1.
    rewrite HeqKL2; perm.
  + apply IHDLI_provable2.
    rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    DLI_reorder_antecedent (PPdisj P1 P2 :: KP1 :: KP2 :: KL2').
    apply DLI_disj_antecedent.
    * DLI_reorder_antecedent (KP1 :: KP2 :: P1 :: KL2').
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * DLI_reorder_antecedent (KP1 :: KP2 :: P2 :: KL2').
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_l.
  apply IHDLI_provable.
  exact HeqKL2.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_r.
  apply IHDLI_provable.
  exact HeqKL2.
Qed.

Lemma DLI_disj_elimL_l:
  forall P1 P2 P3 L1,
    DLI_provable (PPdisj P1 P2::L1) P3 ->
    DLI_provable (P1::L1) P3.
Proof.
intros KP1 KP2 KP3 KL1 H.
remember (PPdisj KP1 KP2::KL1) as KL2.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros KL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2.
  reflexivity.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLI_disj_succedent_l.
    apply DLI_axiom.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_axiom.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_exfalso.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  { congruence. }
  rewrite PrC.
  apply PProp_perm_select in PrD.
  destruct PrD as [(PrE,PrF) | (KL2'',(PrG,PrH))].
  { congruence. }
  rewrite PrG.
  DLI_reorder_antecedent (PPimpl (PPatom A1) P1 :: PPatom A1 :: KP1 :: KL2'').
  apply DLI_impl_antecedent_atom.
  DLI_reorder_antecedent (KP1::P1::PPatom A1::KL2'').
  apply IHDLI_provable.
  rewrite PrH; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_impl.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_conj.
    rewrite perm_swap.
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_disj.
    DLI_reorder_antecedent (KP1 :: PPimpl P2 P1 :: PPimpl P3 P1 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_impl_succedent.
  rewrite perm_swap.
  apply IHDLI_provable.
  rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_conj_antecedent.
    DLI_reorder_antecedent (KP1 :: P1 :: P2 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_conj_succedent.
  + apply IHDLI_provable1.
    rewrite HeqKL2; perm.
  + apply IHDLI_provable2.
    rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP1 with P1 by congruence.
    rewrite <-PrB.
    exact H.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_disj_antecedent.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_l.
  apply IHDLI_provable.
  exact HeqKL2.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_r.
  apply IHDLI_provable.
  exact HeqKL2.
Qed.

Lemma DLI_disj_elimL_r:
  forall P1 P2 P3 L1,
    DLI_provable (PPdisj P1 P2::L1) P3 ->
    DLI_provable (P2::L1) P3.
Proof.
intros KP1 KP2 KP3 KL1 H.
remember (PPdisj KP1 KP2::KL1) as KL2.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros KL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2.
  reflexivity.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLI_disj_succedent_r.
    apply DLI_axiom.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_axiom.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_exfalso.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  { congruence. }
  rewrite PrC.
  apply PProp_perm_select in PrD.
  destruct PrD as [(PrE,PrF) | (KL2'',(PrG,PrH))].
  { congruence. }
  rewrite PrG.
  DLI_reorder_antecedent (PPimpl (PPatom A1) P1 :: PPatom A1 :: KP2 :: KL2'').
  apply DLI_impl_antecedent_atom.
  DLI_reorder_antecedent (KP2::P1::PPatom A1::KL2'').
  apply IHDLI_provable.
  rewrite PrH; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_impl.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_conj.
    rewrite perm_swap.
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_disj.
    DLI_reorder_antecedent (KP2 :: PPimpl P2 P1 :: PPimpl P3 P1 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_impl_succedent.
  rewrite perm_swap.
  apply IHDLI_provable.
  rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_conj_antecedent.
    DLI_reorder_antecedent (KP2 :: P1 :: P2 :: KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_conj_succedent.
  + apply IHDLI_provable1.
    rewrite HeqKL2; perm.
  + apply IHDLI_provable2.
    rewrite HeqKL2; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP2 with P2 by congruence.
    rewrite <-PrB.
    exact H0.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_disj_antecedent.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_l.
  apply IHDLI_provable.
  exact HeqKL2.
- intros KL1 HeqKL2.
  apply DLI_disj_succedent_r.
  apply IHDLI_provable.
  exact HeqKL2.
Qed.

Definition DLI_contr_permselect := DLJ_contr_permselect.

Lemma DLI_contr_withantweak:
  forall P1 P2 L1,
    DLI_provable (P1::P1::L1) P2 -> DLI_provable (P1::L1) P2.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KL1 H.
remember (KP1::KP1::KL1) as KL2 in H.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros OL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2; reflexivity.
- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLI_axiom.
  + rewrite PrC.
    DLI_reorder_antecedent (P1::KP1::KL2').
    apply DLI_axiom.
- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    apply DLI_exfalso.
  + rewrite PrC.
    DLI_reorder_antecedent (PPbot::KP1::KL2').
    apply DLI_exfalso.
- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + apply PProp_perm_select in PrB.
    destruct PrB as [(PrE,PrF) | (KL2',(PrG,PrH))].
    { congruence. }
    rewrite PrG.
    rewrite <-PrA.
    apply DLI_impl_antecedent_atom.
    apply HI_rank.
    { apply (PPsmall_impl_r _ (eq_sym PrA)). }
    
  +

- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLI_impl_antecedent.
      - rewrite PrA.
        apply IHDLI_provable1.
        rewrite PrB,<-PrA; reflexivity.
      - apply HI_rank.
        + apply (PPsmall_impl_r _ (eq_sym PrA)).
        + apply DLI_impl_antecedent_weak with (P1:=P1).
          rewrite PrA.
          rewrite perm_swap.
          rewrite <-PrB.
          exact H0.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLI_impl_succedent.
  rewrite perm_swap.
  apply IHDLI_provable.
  rewrite HeqKL2; perm.
- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLI_conj_antecedent.
      apply HI_rank.
      {
        apply (PPsmall_conj_l _ (eq_sym PrA)).
      }
      DLI_reorder_antecedent (P2::P1::P1::OL1).
      apply HI_rank.
      {
        apply (PPsmall_conj_r _ (eq_sym PrA)).
      }
      DLI_reorder_antecedent (P1::P2::P1::P2::OL1).
      apply DLI_conj_elimL.
      rewrite PrA.
      DLI_reorder_antecedent (P1::P2::KP1::OL1).
      rewrite <-PrB.
      exact H.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_conj_antecedent.
    DLI_reorder_antecedent (KP1::P1::P2::KL2').
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLI_conj_succedent.
  + apply IHDLI_provable1.
    exact HeqKL2.
  + apply IHDLI_provable2.
    exact HeqKL2.
- intros OL1 HeqKL2.
  apply DLI_contr_permselect in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite <-PrA.
    {
      apply DLI_disj_antecedent.
      - apply HI_rank.
        {
          apply (PPsmall_disj_l _ (eq_sym PrA)).
        }
        apply DLI_disj_elimL_l with (P2:=P2).
        rewrite PrA.
        rewrite perm_swap.
        rewrite <-PrB.
        exact H.
      - apply HI_rank.
        {
          apply (PPsmall_disj_r _ (eq_sym PrA)).
        }
        apply DLI_disj_elimL_r with (P1:=P1).
        rewrite PrA.
        rewrite perm_swap.
        rewrite <-PrB.
        exact H0.
    }
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_disj_antecedent.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros OL1 HeqKL2.
  apply DLI_disj_succedent_l.
  apply IHDLI_provable.
  exact HeqKL2.
- intros OL1 HeqKL2.
  apply DLI_disj_succedent_r.
  apply IHDLI_provable.
  exact HeqKL2.
Qed.

Lemma DLI_impl_antecedent_weak:
  forall P1 P2 P3 L1,
    DLI_provable (PPimpl P1 P2::L1) P3 ->
    DLI_provable (P2::L1) P3.
Proof.
induction P1 as (KP1,HI_rank) using (well_founded_ind PProp_small_wellfounded).
intros KP2 KP3 KL1 H.
remember (PPimpl KP1 KP2 :: KL1) as KL2 in H.
apply eq_then_Permutation in HeqKL2.
revert KL1 HeqKL2.
induction H.
- intros KL1 HeqKL2.
  apply IHDLI_provable.
  rewrite H,HeqKL2; reflexivity.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + rewrite PrA.
    apply DLI_impl_succedent.
    rewrite perm_swap.
    apply DLI_axiom.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_axiom.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + congruence.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_exfalso.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP2 with P1 by congruence.
    rewrite <-PrB.
    exact H.
  + apply PProp_perm_select in PrD.
    destruct PrD as [(PrE,PrF) | (KL2'',(PrG,PrH))].
    { congruence. }
    rewrite PrC.
    rewrite PrG.
    DLI_reorder_antecedent (PPimpl (PPatom A1) P1 :: PPatom A1 :: KP2 :: KL2'').
    apply DLI_impl_antecedent_atom.
    DLI_reorder_antecedent (KP2 :: P1 :: PPatom A1 :: KL2'').
    apply IHDLI_provable.
    rewrite PrH; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP2 with P1 by congruence.
    rewrite <-PrB.
    exact H0.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_impl.
    * rewrite perm_swap.
      apply IHDLI_provable1.
      rewrite PrD; perm.
    * rewrite perm_swap.
      apply IHDLI_provable2.
      rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP2 with P1 by congruence.
    rewrite <-PrB.
    apply HI_rank with (y:=P3).
    { apply (PPsmall_conj_r P2); congruence. }
    apply HI_rank with (y:=P2).
    { apply (PPsmall_conj_l P3); congruence. }
    exact H.
  + rewrite PrC.
    rewrite perm_swap.
    apply DLI_impl_antecedent_conj.
    rewrite perm_swap.
    apply IHDLI_provable.
    rewrite PrD; perm.
- intros KL1 HeqKL2.
  apply PProp_perm_select in HeqKL2.
  destruct HeqKL2 as [(PrA,PrB) | (KL2',(PrC,PrD))].
  + replace KP2 with P1 by congruence.
    rewrite <-PrB.
    re
  +
- intros KL1 HeqKL2.
- intros KL1 HeqKL2.
- intros KL1 HeqKL2.
- intros KL1 HeqKL2.
- intros KL1 HeqKL2.
- intros KL1 HeqKL2.
Qed.

Lemma DLI_impl_antecedent2:
  forall P1 P2 P3 L1,
    DLI_provable (P2::P1::L1) P3 ->
    DLI_provable (PPimpl P1 P2::P1::L1) P3.
Proof.
intros KP1.
induction KP1.
- intros KP2 KP3 KL1 H.
  rewrite perm_swap.
  apply DLI_exfalso.
- intros KP2 KP3 KL1 H.
  apply DLI_impl_antecedent_atom.
  exact H.
- intros KP2 KP3 KL1 H.
  apply DLI_impl_antecedent_impl.
  + apply DLI_impl_succedent.
    DLI_reorder_antecedent (PPimpl KP1_1 KP1_2::KP1_1::PPimpl KP1_2 KP2::KL1).
    apply IHKP1_1.
    DLI_reorder_antecedent (PPimpl KP1_2 KP2::KP1_2::KP1_1::KL1).
    apply IHKP1_2.
    DLI_reorder_antecedent (KP1_2::KP2::KP1_1::KL1).
    apply DLI_axiom.
  + exact H.
- intros KP2 KP3 KL1 H.
  apply DLI_impl_antecedent_conj.
  rewrite perm_swap.
  apply DLI_conj_antecedent.
  DLI_reorder_antecedent (PPimpl KP1_1 (PPimpl KP1_2 KP2)::KP1_1::KP1_2::KL1).
  apply IHKP1_1.
  DLI_reorder_antecedent (PPimpl KP1_2 KP2::KP1_2::KP1_1::KL1).
  apply IHKP1_2.
  DLI_reorder_antecedent (KP1_1 :: KP1_2 :: KP2 :: KL1).
  apply DLI_conj_elimL.
  rewrite perm_swap.
  exact H.
- intros KP2 KP3 KL1 H.
  apply DLI_impl_antecedent_disj.
  DLI_reorder_antecedent
    (PPdisj KP1_1 KP1_2::PPimpl KP1_1 KP2::PPimpl KP1_2 KP2 :: KL1).
  apply DLI_disj_antecedent.
  + DLI_reorder_antecedent (PPimpl KP1_1 KP2 :: KP1_1 :: PPimpl KP1_2 KP2 :: KL1).
    apply IHKP1_1.
    DLI_reorder_antecedent (PPimpl KP1_2 KP2 :: KP1_1 :: KP2 :: KL1).
    apply DLI_weak.
    apply DLI_disj_elimL_l with (P2:=KP1_2).
    rewrite perm_swap.
    exact H.
  + DLI_reorder_antecedent (PPimpl KP1_2 KP2 :: KP1_2 :: PPimpl KP1_1 KP2 :: KL1).
    apply IHKP1_2.
    DLI_reorder_antecedent (PPimpl KP1_1 KP2 :: KP1_2 :: KP2 :: KL1).
    apply DLI_weak.
    apply DLI_disj_elimL_r with (P1:=KP1_1).
    rewrite perm_swap.
    exact H.
Qed.

