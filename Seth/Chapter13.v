Require Import ZArith Lia Classical Reals Lra Classical_sets List Ensembles QArith ClassicalFacts Finite_sets.
Import ListNotations.
From Seth Require Export Chapter12 Sums.

Open Scope nat_scope.

Definition induction_nat := forall P : ℕ-> Prop,
  ((P 0 /\ (forall k : ℕ, P k -> P (S k))) -> forall n : ℕ, P n).

Lemma induction_N : induction_nat.
Proof.
  unfold induction_nat.
  intros P [H1 H2] n. induction n as [| k IH].
  - apply H1.
  - apply H2. apply IH.
Qed.

Close Scope nat_scope.
Open Scope R_scope.

Ltac break_INR :=
  repeat match goal with
  | [ |- context[INR (?n + ?m)] ] =>
      rewrite plus_INR
  | [ |- context[INR (?n * ?m)] ] =>
      rewrite mult_INR
  | [ |- context[INR (S ?n)] ] =>
      rewrite S_INR
  | [ |- context[INR (?n - ?m)] ] =>
      rewrite minus_INR
  end.

Ltac convert_nat_to_INR_in_H :=
  try
  match goal with
  | [ H: (?x > ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x < ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x >= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x <= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x = ?y)%nat |- _ ] => apply INR_eq in H; simpl in H
  end.

Ltac solve_INR :=
  convert_nat_to_INR_in_H; try field_simplify_eq; try break_INR; simpl; try field; try nra; try lia.

Lemma lemma_13_1 : forall (n : ℕ),
  sum_f 0 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  induction n as [| k IH].
  - compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH. replace (S k^2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. lia. }
    replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. solve_INR.
Qed.

Lemma lemma_13_1' : forall (n : ℕ),
  (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  intro n. set (P := fun n => (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2)).
  assert (((P 0%nat /\ (forall k : ℕ, P k -> P (S k))) -> forall n : ℕ, P n)) as H1.
  { apply induction_N. } assert (forall n, P n) as H2.
  {
    apply H1. split.
    - unfold P. intros H2. lia.
    - intros k IH. unfold P in IH. unfold P. intros H2. assert (k = 0 \/ (k > 0))%nat as [H3 | H3] by lia.
      -- rewrite H3. rewrite sum_f_n_n. simpl. lra.
      -- rewrite sum_f_i_Sn_f; try lia. specialize (IH H3). rewrite IH. replace (S k^2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. lia. }
         replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. solve_INR.
  }
  specialize (H2 n). unfold P in H2. apply H2.
Qed.

Open Scope R_scope.

Lemma lemma_13_2 : forall (n : ℕ),
  (n > 0)%nat -> sum_f 1 n (fun i => 1 / (INR (2 * i - 1) * INR (2 * i + 1))) = INR n / INR (2 * n + 1).
Proof.
  intros n H1. induction n as [| k IH]; try lia. clear H1. assert (k = 0 \/ k > 0)%nat as [H1 | H1] by lia.
  - rewrite H1. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite (IH H1). solve_INR.
Qed.

Lemma lemma_13_3 : forall n : nat,
  (n > 0)%nat -> sum_f 1 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. solve_INR.
Qed.

Open Scope nat_scope.

Lemma lemma_13_a : forall n : ℕ,
  n > 0 -> n < 3^n.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (k = 0 \/ k > 0) as [H2 | H2] by lia.
  - rewrite H2. compute. lia.
  - specialize (IH H2). replace (3^S k) with (3 * 3^k) by (simpl; lia). replace (S k) with (k + 1) by lia. lia.
Qed.

Open Scope Z_scope.

Lemma lemma_13_b : forall n : Z, n < 3^n.
Proof.
  intros n. assert (n = 0 \/ n > 0 \/ n < 0) as [H1 | [H1 | H1]] by lia.
  - rewrite H1. simpl. lia.
  - pose proof (lemma_13_a (Z.to_nat n)) as H2. assert (Z.to_nat n > 0)%nat as H3 by lia. specialize (H2 H3). apply inj_lt in H2.
    replace n with (Z.of_nat (Z.to_nat n)) at 1 by lia. rewrite inj_pow in H2. simpl in H2. rewrite Z2Nat.id in H2; lia.
  - assert (3^n = 0). { apply Z.pow_neg_r; lia. } lia.
Qed.

Open Scope R_scope.

Lemma lemma_13_5 : forall n r,
  r <> 1 -> sum_f 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
Proof.
  intros n r H1. induction n as [| k IH].
  - compute. field. nra.
  - destruct k as [| k'] eqn : Ek.
    -- compute. field. nra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite <- Ek. apply Rmult_eq_reg_l with (r := (1 - r)).
       2 : { nra. }
       replace ((1 - r) * ((1 - r ^ (k + 1)) / (1 - r) + r ^ S k)) with (1 - r^(k+1) + r^S k - r * r^S k) by (field; nra).
       replace ((1 - r) * ((1 - r ^ (S k + 1)) / (1 - r))) with (1 - r^(S k + 1)) by (field; nra).
       replace (r^(S k + 1)) with (r * r ^ (S k)). 2 : { replace (S k + 1)%nat with (S (S k)) by lia. simpl. auto. }
       simpl. apply Rplus_eq_reg_r with (r := r * (r * r^k)).
       replace (1 - r ^ (k + 1) + r * r ^ k - r * (r * r ^ k) + r * (r * r ^ k)) with
               (1 - r ^(k+1) + r * r^k) by nra.
       replace (1 - r * (r * r ^ k) + r * (r * r ^ k)) with 1 by nra.
       replace (k+1)%nat with (S k) by lia. simpl. lra.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_lt_1 : forall r n,
  0 < r < 1 -> (n > 0)%nat -> r ^ n < 1.
Proof.
  intros r n [H1 H2] H3. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k < 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_gt_1 : forall r n,
  r > 1 -> (n > 0)%nat -> r ^ n > 1.
Proof.
  intros r n H1 H2. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k > 1) by (apply IH; lia). nra.
Qed.

Lemma lemma_13_6 : forall n h,
  h > -1 -> (1 + h) ^ n >= 1 + INR n * h.
Proof.
  intros n h H1. induction n as [| k IH].
  - simpl. lra.
  - pose proof (Rtotal_order h 0) as [H2 | [H2 | H2]].
    -- rewrite S_INR. replace ((1+h)^S k) with ((1 + h)^k + h * (1 + h)^k) by (simpl; lra).
       replace (1 + (INR k + 1) * h) with (1 + INR k * h + h) by lra. assert ((1 + h)^k > 0) as H3 by (apply Rpow_gt_0; nra).
       destruct k. { compute. lra. } assert ((1 + h) ^ S k < 1) as H4 by (apply Rpow_lt_1; try nra; try lia). nra.
    -- simpl. nra.
    -- rewrite S_INR. replace ((1+h)^S k) with ((1 + h)^k + h * (1 + h)^k) by (simpl; lra).
       replace (1 + (INR k + 1) * h) with (1 + INR k * h + h) by lra. assert ((1 + h)^k > 0) as H3 by (apply Rpow_gt_0; nra).
       destruct k. { compute. lra. } assert ((1 + h) ^ S k > 1) as H4 by (apply Rpow_gt_1; try nra; try lia). nra.
Qed.

Proposition prop_13_11 : forall (A : Ensemble R),
  A ≠ ∅ -> (exists l : list R, list_to_ensemble l = A) -> exists r, r ∈ A /\ forall r', r' ∈ A -> r <= r'.
Proof.
  intros A H1 [l H2]. generalize dependent A. induction l as [| h t IH].
  - intros A H1 H2. simpl in H2. rewrite H2 in H1. exfalso. apply H1. reflexivity.
  - intros A H1 H2. rewrite list_to_ensemble_cons in H2. set (T := list_to_ensemble t).
    assert (T = ∅ \/ T ≠ ∅) as [H3 | H3] by apply classic.
    -- unfold T in H3. rewrite H3 in H2. rewrite Union_comm in H2. rewrite Union_Identity in H2.
       exists h. split. rewrite set_equal_def in H2. specialize (H2 h) as [H2 _]. apply H2. apply In_singleton.
       intros r' H4. rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H4). apply Singleton_inv in H2. lra.
    -- specialize (IH (list_to_ensemble t) H3 eq_refl) as [r [IH1 IH2]]. assert (h <= r \/ h > r) as [H4 | H4] by lra.
        + exists h. split.
          ++ rewrite set_equal_def in H2. specialize (H2 h) as [H2 _]. apply H2. apply In_Union_def. left. apply In_singleton.
          ++ intros r' H5. specialize (IH2 r'). rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H5).
             apply In_Union_def in H2 as [H2 | H2].
             * apply Singleton_inv in H2. lra.
             * specialize (IH2 H2). lra.
        + exists r. split.
          ++ rewrite set_equal_def in H2. specialize (H2 r) as [H2 _]. apply H2. apply In_Union_def. right. apply IH1.
          ++ intros r' H5. rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H5). apply In_Union_def in H2 as [H2 | H2].
             * apply Singleton_inv in H2. lra.
             * apply IH2. apply H2.
Qed.

Lemma exists_nat_list_exists_R_list : forall (l : list ℕ),
  exists l' : list R, list_to_ensemble l' = list_to_ensemble (map INR l).
Proof.
  induction l as [| h t IH].
  - exists []. reflexivity.
  - destruct IH as [l' IH]. exists (INR h :: l'). simpl. rewrite IH. reflexivity.
Qed.

Open Scope nat_scope.

Lemma lemma_13_7 : forall (A : Ensemble ℕ),
  A ≠ ∅ -> (exists l : list ℕ, list_to_ensemble l = A) -> exists n, n ∈ A /\ forall n', n' ∈ A -> n <= n'.
Proof.
  intros A H1 [l H2]. destruct (exists_nat_list_exists_R_list l) as [l' H3]. specialize (prop_13_11 (list_to_ensemble l')).
  intros H4. assert (H5 : list_to_ensemble l' ≠ ∅). 
  { rewrite H3. apply list_to_ensemble_map_not_empty. apply list_to_ensemble_not_empty. rewrite H2. auto. }
   specialize (H4 H5) as [r [H6 H7]].
  - exists l'. auto.
  - assert (exists n : ℕ, INR n = r) as [n H8].
    {
      pose proof in_map_iff INR l r as [H8 _]. rewrite In_list_to_ensemble in H8.
      rewrite <- H3 in H8. specialize (H8 H6) as [x [H8 _]]. exists x. auto.
    }
    exists n. split.
    -- rewrite <- H2. apply In_list_to_ensemble. apply In_list_to_ensemble in H6. pose proof (in_map_iff) as H9. specialize (H9 ℕ R).
       specialize (H9 INR l r). rewrite list_to_ensemble_eq_iff in H3. specialize (H3 r) as [H3 _]. specialize (H3 H6).
       destruct H9 as [H9 _]. specialize (H9 H3) as [x [H9 H10]]. replace n%nat with x%nat. auto. apply INR_eq. lra.
    -- intros n' H9. 
Admitted.