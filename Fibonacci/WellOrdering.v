Require Import Coq.ZArith.ZArith Lia Classical.
From Fibonacci Require Import Strong_Induction.

Open Scope nat_scope.

Lemma well_ordering_principle_contrapositive_nat : forall E : nat -> Prop,
  (~(exists m, E m /\ forall k, E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E H.
  set (E' := fun n => ~ E n).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split. apply H2. intros k H3. lia. }
  assert (H2: forall n, E' n).
  { 
    intros n. apply strong_induction. intros m H2. destruct m.
    - unfold E'. unfold not. apply H0.
    - assert (E (S m) -> False).
      { intros H3. apply H. exists (S m). split. apply H3. intros k H4.
        specialize (H2 k). assert (E' k -> False). unfold E'. 
        unfold not. intros H5. apply H5. apply H4. assert (k < S m -> False) by auto.
        lia. 
      }
      unfold E'. unfold not. apply H1.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply H3.
Qed.

Theorem well_ordering_nat : forall E : nat -> Prop,
  (exists x, E x) -> 
  (exists n, E n /\ forall m, E m -> (n <= m)).
Proof.
  intros E. 
  assert (H :
    ~(exists m, E m /\ forall k, E k -> m <= k) ->
      ~(exists n, E n)) by apply well_ordering_principle_contrapositive_nat.
  
  intros [x Ex].
  destruct (classic (exists m, E m /\ forall k, E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex.
Qed.

Open Scope Z_scope.

Lemma well_ordering_principle_contrapositive_Z : forall E : Z -> Prop,
  (forall n : Z, E n -> n >= 0) ->
  (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E Hnon_neg H.
  set (E' := fun z => ~ E z).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split; try split.
    - apply H2.
    - intros k _ H3. specialize (Hnon_neg k). apply Hnon_neg in H3. lia.
  }
  assert (H2: forall z, z >= 0 -> E' z).
  { 
    intros z Hz. apply strong_induction_Z. intros m H2. destruct (Z_le_dec m 0).
    - unfold E'. unfold not. apply Z_le_lt_eq_dec in l. destruct l.
      -- specialize (Hnon_neg m). intros H3. apply Hnon_neg in H3. lia.
      -- rewrite e. apply H0.
    - assert (E m -> False).
      { intros H3. apply H. exists m. split; try split.
        - apply H3.
        - intros k H4 H5. specialize (H2 k). assert (E' k -> False). unfold E'. 
          unfold not. intros H6. apply H6. apply H5. assert (0 <= k < m -> False) by auto.
          lia. 
      }
      unfold E'. unfold not. apply H1.
    - lia.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply Hnon_neg in H3. apply H3. apply H3.
Qed.

Theorem well_ordering_Z : forall E : Z -> Prop,
  (forall z, E z -> z >= 0) ->
  (exists x, E x) -> 
  (exists n, E n /\ forall m, m >= 0 -> E m -> (n <= m)).
Proof.
  intros E Hnon_neg [x Ex]. 
  assert (H :
    (forall n : Z, E n -> n >= 0) ->
      (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
      (~(exists n, E n))).
    { apply well_ordering_principle_contrapositive_Z. }
  
  destruct (classic (exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex. apply Hnon_neg. 
Qed.
