Require Import Lia.

Lemma strong_induction (P : nat -> Prop) :
  P 0 ->
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros H1 H2 n. enough (H0: forall k, k <= n -> P k).
  - apply H0. lia.
  - induction n.
    -- intros k Hk. inversion Hk. apply H1.
    -- intros k Hk. apply H2. intros k' Hk'. apply IHn. lia.
Qed.