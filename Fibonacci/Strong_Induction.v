Require Import Lia.

Lemma strong_induction (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros H1 n. assert (H2: forall k, k <= n -> P k).
  - induction n.
    -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
    -- intros k Hk. apply H1. intros k' Hk'. apply IHn. lia.
  - apply H2. lia.
Qed.