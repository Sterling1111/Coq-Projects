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

Definition f_even (f : R -> R) := forall x : R, f x = f (-x).
Definition f_odd (f : R -> R) := forall x : R, f x = -f (-x).

Definition function_addition_R (f g: R -> R) (x : R) : R :=
  f x + g x.

Definition function_subtraction_R (f g: R -> R) (x : R) : R :=
  f x - g x.

Definition function_multiplication_R (f g: R -> R) (x : R) : R :=
  f x * g x.

Definition function_division_R (f g: R -> R) (x : R) : R :=
  f x / g x.

Definition function_composition_R (f g: R -> R) (x : R) : R :=
  f (g x).

Definition function_multiplication_by_constant_R (f: R -> R) (c: R) (x: R) : R :=
  c * f x.

(* Function addition *)
Notation "f + g" := (function_addition_R f g) (at level 50, left associativity) : function_scope.

(* Function subtraction *)
Notation "f - g" := (function_subtraction_R f g) (at level 50, left associativity) : function_scope.

(* Function multiplication *)
Notation "f ∙ g" := (function_multiplication_R f g) (at level 40, left associativity) : function_scope.

(* Function division *)
Notation "f / g" := (function_division_R f g) (at level 40, left associativity) : function_scope.

(* Function composition *)
Notation "f ∘ g" := (function_composition_R f g) (at level 30, right associativity) : function_scope.

(* Multiplication by a constant *)
Notation "c * f" := (function_multiplication_by_constant_R f c) (at level 40, left associativity) : function_scope.

Lemma lemma_3_12_a_i : forall (f g : R -> R), f_even f -> f_even g -> f_even (f + g).
Proof.
  intros f g H1 H2. unfold function_addition_R. unfold f_even in *. intros x. rewrite <- H1, <- H2. nra.
Qed.

Lemma lemma_3_12_a_ii : (forall (f g : R -> R), f_even f -> f_odd g -> f_odd (f + g)) -> False.
Proof.
  intros H1. specialize (H1 (fun x => x) (fun x => -x)). unfold f_even, f_odd in *. specialize (H1 (fun x => x) (fun x => -x)). simpl in H1. specialize (H1 1). nra.