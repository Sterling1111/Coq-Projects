Require Import ZArith Lia Classical Reals Lra Classical_sets List Ensembles QArith ClassicalFacts Finite_sets.
Import ListNotations.
From Seth Require Export Chapter13 Sums.

(* just do std lib Power_Set dont use this*)
Definition Power_Set {U : Type} (A : Ensemble U) : Ensemble (Ensemble U) :=
  fun B => B ⊆ A.

Definition Finite_Set {U : Type} (A : Ensemble U) : Prop :=
  exists n : ℕ, exists l : list U, FromList l = A.

Proposition prop_14_6 : forall (U : Type) (A : Ensemble U) (n : ℕ),
  Finite_Set A -> cardinal U A n -> cardinal (Ensemble U) (Power_Set A) (2^n).
Proof.
  intros U A n [m [l H1]] H2. induction l as [| h t IH].
  - rewrite FromList_list_to_ensemble in H1. simpl in H1. rewrite <- H1. unfold Power_Set.

Admitted.

Open Scope nat_scope.

Lemma lemma_14_1 : forall n : nat,
  n >= 7 -> fact n > 3^n.
Proof.
  intros n H1. induction n as [| n IH]; try lia.
  assert (S n = 7 \/ n >= 7) as [H2 | H2] by lia.
  - rewrite H2. compute; lia.
  - rewrite fact_simpl. specialize (IH H2). rewrite Nat.pow_succ_r'. apply Nat.mul_lt_mono; lia.
Qed.

Lemma lemma_14_2 : forall n : nat,
  n >= 6 -> fact n > n^3.
Proof.
  intros n H1. induction n as [| n IH]; try lia.
  - assert (S n = 6 \/ n >= 6) as [H2 | H2] by lia.
    + rewrite H2. compute. lia.
    + rewrite fact_simpl. specialize (IH H2). replace (S n ^ 3) with (n^3 + (3 * n^2 + 3 * n + 1)) by (simpl; nia).
      replace (S n * fact n) with (fact n + n * fact n) by lia.
      apply Nat.add_lt_mono; try lia.
Qed.

Lemma lemma_14_4 : forall (l : list Prop),
  ~ (fold_right and True l) -> fold_right or False (map (fun P => ~ P) l).
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. exfalso. apply H1. apply I.
  - rewrite map_cons. replace (((~ h) :: map (fun P : Prop => ~ P) t)) with ([~ h] ++ map (fun P : Prop => ~ P) t) by reflexivity.
    rewrite fold_right_app. simpl. replace (h :: t) with ([h] ++ t) in H1 by reflexivity. rewrite fold_right_app in H1. simpl in H1.
    apply not_and_or in H1 as [H2 | H2].
    -- left. auto.
    -- right. apply (IH H2).
Qed.