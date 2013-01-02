Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Lemma app_compat_perm_latter(A:Type) : forall l a1 a2:list A, Permutation a1 a2 -> Permutation (l++a1) (l++a2).
Proof.
intros l a1 a2 Ha.
induction l.
- exact Ha.
- apply perm_skip,IHl.
Qed.

Instance app_compat_perm(A:Type) : Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
Proof.
unfold Proper,respectful.
intros a1 a2 Ha b1 b2 Hb.
induction Ha.
- exact Hb.
- apply perm_skip.
  exact IHHa.
- apply perm_trans with ((x::y::l)++b1).
  + apply perm_swap.
  + apply perm_skip,perm_skip,app_compat_perm_latter,Hb.
- apply perm_trans with (l'++b2); [exact IHHa1|].
  apply perm_trans with (l'++b1); [|exact IHHa2].
  apply app_compat_perm_latter,Permutation_sym,Hb.
Qed.

Lemma Permutation_In_In: forall{A:Type} (x:A) (l1 l2:list A), Permutation l1 l2 -> In x l1 -> In x l2.
Proof.
intros A x l1 l2 HP H.
induction HP.
- exact H.
- destruct H as [H|H].
  + left.
    exact H.
  + right.
    apply IHHP,H.
- destruct H as [H|[H|H]].
  + right.
    left.
    exact H.
  + left.
    exact H.
  + right.
    right.
    exact H.
- apply IHHP2,IHHP1,H.
Qed.

Instance In_compat_perm(A:Type)
  (eq_dec: forall x y:A, {x=y} + {x<>y}):
    Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof.
unfold Proper,respectful.
intros x1 x2 Hx l1 l2 Hl.
rewrite Hx; clear x1 Hx.
split.
- apply Permutation_In_In,Hl.
- apply Permutation_In_In.
  symmetry.
  exact Hl.
Qed.

Lemma app_normalize_1:
  forall(A:Type) (l1 l2 l3:list A),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros A l1 l2 l3.
rewrite app_assoc.
reflexivity.
Qed.

Lemma app_normalize_2:
  forall(A:Type) (a1:A) (l2 l3:list A),
    (a1 :: l2) ++ l3 = a1 :: (l2 ++ l3).
Proof.
intros; reflexivity.
Qed.

Lemma app_normalize_3:
  forall(A:Type) (l1:list A), (nil++l1) = l1.
Proof.
intros; reflexivity.
Qed.

Ltac app_normalize := repeat (
  rewrite app_normalize_1 || 
  rewrite app_normalize_2 ||
  rewrite app_normalize_3).

Lemma perm_takeit_1:
  forall(A:Type) (target:list A) (l1 l2:list A),
    Permutation (l1 ++ (target ++ l2)) (target ++ (l1 ++ l2)).
Proof.
intros A target l1 l2.
rewrite (app_assoc l1 target l2),
  (Permutation_app_comm l1 target),
  <-(app_assoc target l1 l2).
reflexivity.
Qed.

Lemma perm_takeit_2:
  forall(A:Type) (target:list A) (a1:A) (l2:list A),
    Permutation (a1 :: (target ++ l2)) (target ++ (a1 :: l2)).
Proof.
intros A target a1 l2.
apply (perm_takeit_1 _ _ (a1::nil)).
Qed.

Lemma perm_takeit_3:
  forall(A:Type) (target:list A) (l1:list A),
    Permutation (l1 ++ target) (target ++ l1).
Proof.
intros A target l1.
apply Permutation_app_comm.
Qed.

Lemma perm_takeit_4:
  forall(A:Type) (target:list A) (a1:A),
    Permutation (a1 :: target) (target ++ (a1::nil)).
Proof.
intros A target a1.
apply (perm_takeit_3 _ _ (a1::nil)).
Qed.

Lemma perm_takeit_5:
  forall(A:Type) (target:A) (l1 l2:list A),
    Permutation (l1 ++ (target :: l2)) (target :: (l1 ++ l2)).
Proof.
intros A target l1 l2.
apply (perm_takeit_1 _ (target::nil)).
Qed.

Lemma perm_takeit_6:
  forall(A:Type) (target:A) (a1:A) (l2:list A),
    Permutation (a1 :: (target :: l2)) (target :: (a1 :: l2)).
Proof.
intros A target a1 l2.
apply (perm_takeit_2 _ (target::nil)).
Qed.

Lemma perm_takeit_7:
  forall(A:Type) (target:A) (l1:list A),
    Permutation (l1 ++ (target::nil)) (target :: l1).
Proof.
intros A target l1.
apply (perm_takeit_3 _ (target::nil)).
Qed.

Lemma perm_takeit_8:
  forall(A:Type) (target:A) (a1:A),
    Permutation (a1 :: (target::nil)) (target :: (a1::nil)).
Proof.
intros A target a1.
apply (perm_takeit_4 _ (target::nil)).
Qed.

(* Ltac perm_simplify := app_normalize; repeat (
  rewrite app_nil_r ||
  match goal with
  | [ |- Permutation ?L1 ?L1 ] => reflexivity
  | [ |- Permutation (?A1++_) (?A1++_) ] => apply Permutation_app_head
  | [ |- Permutation (?A1::_) (?A1::_) ] => apply perm_skip
  | [ |- Permutation (?L1++_) _ ] => (
      rewrite (perm_takeit_1 _ L1) ||
      rewrite (perm_takeit_2 _ L1) ||
      rewrite (perm_takeit_3 _ L1) ||
      rewrite (perm_takeit_4 _ L1) )
  | [ |- Permutation (?A1::_) _ ] => (
      rewrite (perm_takeit_5 _ A1) ||
      rewrite (perm_takeit_6 _ A1) ||
      rewrite (perm_takeit_7 _ A1) ||
      rewrite (perm_takeit_8 _ A1) )
  end). *)

Ltac perm_simplify := app_normalize; repeat (
  rewrite app_nil_r ||
  match goal with
  | [ |- Permutation ?L1 ?L1 ] => reflexivity
  | [ |- Permutation (?A1++_) (?A1++_) ] => apply Permutation_app_head
  | [ |- Permutation (?A1::_) (?A1::_) ] => apply perm_skip
  | [ |- Permutation _ (?L1++_) ] => (
      rewrite (perm_takeit_1 _ L1) at 1 ||
      rewrite (perm_takeit_2 _ L1) at 1 ||
      rewrite (perm_takeit_3 _ L1) at 1 ||
      rewrite (perm_takeit_4 _ L1) at 1 )
  | [ |- Permutation _ (?A1::_) ] => (
      rewrite (perm_takeit_5 _ A1) at 1 ||
      rewrite (perm_takeit_6 _ A1) at 1 ||
      rewrite (perm_takeit_7 _ A1) at 1 ||
      rewrite (perm_takeit_8 _ A1) at 1 )
  | [ |- Permutation _ _ ] => fail
  end).

Ltac perm :=
  match goal with
  | [ |- Permutation _ _ ] => perm_simplify; fail "perm failed"
  | [ |- _ ] => fail "perm can't solve this system."
  end.

Lemma perm_test: forall(A:Type)
   (a b c d e f:A)
   (p q r s:list A),
     Permutation (a::q++c::(e::p++s)++r++d::r++f::b::q) ((p++c::q++r)++f::b::q++r++a::s++e::d::nil).
Proof.
intros.
perm.
Qed.

Lemma perm_test2: forall(A:Type)
   (a b:list A),
     Permutation (a++b++b) (b++b++a).
Proof.
intros.
perm.
Qed.