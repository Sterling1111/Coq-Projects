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
  intros U A n [m [l H1]] H2. 
Admitted.

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