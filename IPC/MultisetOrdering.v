Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Arith.Arith.
Require Import omega.Omega.
Require Import MyPermutations.

Section MultisetOrderingTr.

Hypothesis A:Type.
Hypothesis R: relation A.
Hypothesis R_wf: well_founded R.

Definition multiset_ordering(L1 L2:list A):Prop :=
  exists LH LT1 LT2,
    (Permutation L1 (LH ++ LT1) /\
     Permutation L2 (LH ++ LT2)) /\
    (exists P2:A, In P2 LT2) /\
    forall P1:A, In P1 LT1 ->
      exists P2:A, In P2 LT2 /\
        R P1 P2.

Definition upper_bound_list :=
  list { ub : A & { l : list A |
    forall a:A, In a l -> clos_refl_trans _ R a ub
  }}.

Fixpoint flatten_upper_bound_list(ubl:upper_bound_list) :=
  match ubl with
  | nil => nil
  | existT _ (exist l _) :: ubl' => l ++ flatten_upper_bound_list ubl'
  end.

Theorem multiset_ordering_wf: well_founded multiset_ordering.
Proof.
intros L.
assert (exists ubl, Permutation L (flatten_upper_bound_list ubl)).
{
  induction L as [|a L (ubl,IHL)].
  - exists nil.
    reflexivity.
  - assert (H: forall b:A, In b (a::nil) -> clos_refl_trans _ R b a).
    {
      intros b [H|[]].
      rewrite H.
      apply rt_refl.
    }
    exists (existT _ a (exist _ (a::nil) H) :: ubl).
    simpl.
    apply Permutation_cons.
    exact IHL.
}
destruct H as (ubl,Hubl).

Qed.

End MultisetOrderingTr.
