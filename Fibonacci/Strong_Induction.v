Require Import Lia ZArith.

Lemma strong_induction :
  forall P : nat -> Prop,
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros P H1 n. assert (H2: forall k, k <= n -> P k).
  - induction n.
    -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
    -- intros k Hk. apply H1. intros k' Hk'. apply IHn. lia.
  - apply H2. lia.
Qed.

Open Scope Z_scope.

Require Import ZArith.
Open Scope Z_scope.

Check Z2Nat.id.

Lemma Z_ind_pos: 
  forall (P: Z -> Prop),
  P 0 ->
  (forall z, z >= 0 -> P z -> P (z + 1)) ->
  forall z, z >= 0 -> P z.
Proof.
  intros P H0 Hstep z Hnonneg.
  
  (* Convert the problem to induction over natural numbers *)
  remember (Z.to_nat z) as n eqn:Heq.
  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hstep. lia. apply IHn1. 
  }
  
  specialize(Hnneg n). rewrite Heq in Hnneg. 
  replace (Z.of_nat (Z.to_nat z)) with (z) in Hnneg. apply Hnneg.
  rewrite Z2Nat.id. lia. lia.
Qed.

Lemma Z_induction_bidirectional :
  forall P : Z -> Prop,
  P 0 ->
  (forall n : Z, P n -> P (n + 1)) ->
  (forall n : Z, P n -> P (n - 1)) ->
  forall n : Z, P n.
Proof.
  intros P H0 Hpos Hneg n.
  
  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hpos. apply IHn1.
  }

  destruct (Z_lt_le_dec n 0).
  - replace n with (- Z.of_nat (Z.to_nat (- n))) by 
      (rewrite Z2Nat.id; lia).
    induction (Z.to_nat (-n)).
    + simpl. apply H0.
    + replace (S n0) with (n0 + 1)%nat by lia. rewrite Nat2Z.inj_add.
      replace (- (Z.of_nat n0 + Z.of_nat 1)) with (-Z.of_nat n0 - 1) by lia. apply Hneg. apply IHn0.
  - apply Z_ind_pos.
    -- apply H0.
    -- intros z H. apply Hpos.
    -- lia.
Qed.

Lemma strong_induction_Z :
  forall P : Z -> Prop,
  (forall m, (forall k : Z, 0 <= k < m -> P k) -> P m) ->
  forall n, 0 <= n -> P n.
Proof.
  intros P H1 n H2. assert (H3: forall k, 0 <= k < n -> P k).
  - apply Z_induction_bidirectional with (n := n).
    -- lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
  - apply H1. intros k Hk. apply H3. lia.
Qed.

