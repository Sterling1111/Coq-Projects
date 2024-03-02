Require Import Reals Lra Lia ZArith FunctionalExtensionality List Classical Arith QArith.
Import ListNotations.
From Spivak Require Export Chapter2.

Section section_3_2.
  Variable h : R -> R.

  Hypothesis H1 : forall x, rational x -> h x = 0.
  Hypothesis H2 : forall x, irrational x -> h x = 1.

  Definition g (x : R) : R := x^2.

End section_3_2.

Lemma lemma_3_16_a : forall (f : R -> R) l,
  (forall x y, f(x + y) = f x + f y) -> f(standard_sum l) = standard_sum (map f l).
Proof.
  intros f l.
  induction l as [|a l IHl].
  - intros H1. simpl. specialize (H1 0 0). rewrite Rplus_0_r in H1. nra.
  - intros H1. simpl. destruct l.
    -- simpl. reflexivity.
    -- simpl. rewrite H1. apply Rplus_eq_compat_l. simpl in IHl. apply IHl. apply H1.
Qed.

Fixpoint f_repeat (f : R -> R) (n : nat) (x : R) : R := 
  match n with
  | O => x
  | S n' => f (f_repeat f n' x)
  end.
  
Lemma lemma_3_11_a : forall H y,
  H (H y) = y -> f_repeat H 80 y = y.
Proof.
  intros H y H1. compute. repeat rewrite H1. reflexivity.
Qed.

Lemma lemma_3_11_b : forall H y,
  H (H y) = y -> f_repeat H 81 y = H y.
Proof.
  intros H y H1. compute. repeat rewrite H1. reflexivity.
Qed.

Lemma lemma_3_11_c : forall H y,
  H (H y) = H y -> f_repeat H 80 y = H y.
Proof.
  intros H y H1. compute. repeat rewrite H1. reflexivity.
Qed.