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

Inductive PProp_small(a b:PProp):Prop :=
  | PPsmall_impl_l x: b = PPimpl a x -> PProp_small a b
  | PPsmall_impl_r x: b = PPimpl x a -> PProp_small a b
  | PPsmall_conj_l x: b = PPconj a x -> PProp_small a b
  | PPsmall_conj_r x: b = PPconj x a -> PProp_small a b
  | PPsmall_disj_l x: b = PPdisj a x -> PProp_small a b
  | PPsmall_disj_r x: b = PPdisj x a -> PProp_small a b.

Arguments PPsmall_impl_l [a] [b] x H.
Arguments PPsmall_impl_r [a] [b] x H.
Arguments PPsmall_conj_l [a] [b] x H.
Arguments PPsmall_conj_r [a] [b] x H.
Arguments PPsmall_disj_l [a] [b] x H.
Arguments PPsmall_disj_r [a] [b] x H.

Lemma PProp_small_wellfounded: well_founded PProp_small.
Proof.
intros p.
induction p.
- exists.
  intros y Hy.
  destruct Hy as [z Hz|z Hz|z Hz|z Hz|z Hz|z Hz]; congruence.
- exists.
  intros y Hy.
  destruct Hy as [z Hz|z Hz|z Hz|z Hz|z Hz|z Hz]; congruence.
- exists.
  intros y Hy.
  destruct Hy as [z Hz|z Hz|z Hz|z Hz|z Hz|z Hz]; congruence.
- exists.
  intros y Hy.
  destruct Hy as [z Hz|z Hz|z Hz|z Hz|z Hz|z Hz]; congruence.
- exists.
  intros y Hy.
  destruct Hy as [z Hz|z Hz|z Hz|z Hz|z Hz|z Hz]; congruence.
Qed.