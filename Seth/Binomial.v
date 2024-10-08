Require Import Reals Lra Lia FunctionalExtensionality.
From Seth Require Import Sums.

Definition is_natural (r : R) : Prop :=
    exists n : nat, r = INR n.

Lemma is_natural_plus : forall r1 r2 : R,
  is_natural r1 -> is_natural r2 -> is_natural (r1 + r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [n1 H1]. destruct H2 as [n2 H2]. exists (n1 + n2)%nat. rewrite H1, H2. rewrite plus_INR. reflexivity.
Qed.

Lemma is_natural_sum_n_nat : forall n : nat,
  (n >= 1)%nat -> is_natural (sum_f 1 n (fun i => INR i)).
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. exists 1%nat. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. apply is_natural_plus; auto. exists (S k). reflexivity.
Qed.

Lemma nltb_gt : forall a b : nat, (a > b)%nat <-> (a <=? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.leb_spec a b); try lia. 
Qed.

Lemma nltb_ge : forall a b : nat, (a >= b)%nat <-> (a <? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.ltb_spec a b); try lia.
Qed.

Module Binomial_R.
  Open Scope R_scope.

  Definition choose (n k : nat) : R :=
    if (n <? k) then 0 else
    (INR (fact n)) / (INR (fact k) * INR (fact (n - k))).

  Module Choose_R_Notations.

    Notation "n ∁ r" := (choose n r) (at level 10).

  End Choose_R_Notations.

  Import Choose_R_Notations.

  Lemma n_choose_n : forall (n : nat),
    n ∁ n = 1.
  Proof.
    intro n. unfold choose. replace (n - n)%nat with 0%nat by lia.
    simpl. rewrite Rmult_1_r. rewrite Nat.ltb_irrefl.
    field. apply INR_fact_neq_0.
  Qed.

  Lemma Sn_choose_n : forall (n : nat),
    (S n) ∁ n = INR (S n).
  Proof.
    intro n. unfold choose. assert (S n <? n = false) as H1. apply Nat.ltb_ge. lia. rewrite H1. replace (S n - n)%nat with 1%nat by lia.
    replace (fact 1) with 1%nat by reflexivity. replace (fact (S n)) with ((S n) * fact n)%nat. 2 : { simpl. reflexivity. }
    rewrite mult_INR. unfold Rdiv. rewrite Rmult_assoc. field_simplify. replace (INR 1) with 1 by reflexivity. nra. split. apply not_0_INR. lia. apply not_0_INR.
    apply fact_neq_0.
  Qed.

  Lemma n_choose_0 : forall (n : nat),
    n ∁ 0 = 1.
  Proof.
    intro n. unfold choose. simpl. rewrite Nat.sub_0_r. rewrite Rmult_1_l.
    field. apply INR_fact_neq_0.
  Qed.

  Lemma O_choose_n : forall (n : nat),
    (n <> 0)%nat -> 0 ∁ n = 0.
  Proof.
    intros n H1. unfold choose. simpl. destruct n; try lia; simpl. lra.
  Qed.

  Lemma k_gt_n_n_choose_k : forall n k : nat,
    (n < k)%nat -> n ∁ k = 0.
  Proof.
    intros. assert (H2 : n <? k = true).
    { apply Nat.ltb_lt. apply H. }
    unfold choose. rewrite H2. reflexivity.
  Qed.

  Lemma n_choose_k_def : forall n k : nat,
    (n >= k)%nat -> n ∁ k = INR (fact n) / (INR (fact k) * INR (fact (n - k))).
  Proof.
    intros n k H1. unfold choose. apply nltb_ge in H1. rewrite H1. reflexivity.
  Qed.

  Lemma fact_div' : forall m n k,
    (k >= 1)%nat -> (m <> 0) -> n / ((INR (fact (k - 1))) * m)  = (n * INR (k)) / (INR (fact k) * m).
  Proof.
    intros m n k H1 H2. destruct k.
    - lia.
    - destruct k.
      -- simpl. lra.
      -- replace (fact (S (S k))) with ((S (S k)) * fact (S k))%nat. 2 : { simpl. lia. }
        replace (S (S k) - 1)%nat with (S ((S k) - 1))%nat. 2 : { simpl. lia. }
      replace (S (S k - 1))%nat with (S k) by lia. unfold Rdiv.
      replace (n * INR (S (S k)) * / (INR (S (S k) * fact (S k)) * m)) with (n * / (INR (fact (S k)) * m)).
      2 : { rewrite mult_INR. field. split. pose proof fact_neq_0 as H3. apply H2. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. lia. }
      reflexivity.
  Qed.

  Lemma binomial_recursion_R_1 : forall n k : nat,
    (k >= 1)%nat -> (S n) ∁ k = n ∁ (k - 1) + n ∁ k.
  Proof.
    intros. assert (H2 : (S n < k \/ S n = k \/ S n > k)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
    - repeat rewrite k_gt_n_n_choose_k. lra. lia. lia. lia.
    - assert (H3 : (n = k - 1)%nat) by lia. rewrite <- H3. rewrite H2. repeat rewrite n_choose_n.
      rewrite k_gt_n_n_choose_k. lra. lia.
    - unfold choose at 2.
      assert (H3 : (n >= k - 1)%nat) by lia. pose proof H3 as H4. apply nltb_ge in H4.
      rewrite H4. unfold choose at 2. assert (H5 : (n >= k)%nat) by lia. pose proof H5 as H6.
      apply nltb_ge in H6. rewrite H6. rewrite fact_div'. 2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
      assert (H7: (n = k)%nat \/ (n > k)%nat) by lia. destruct H7 as [H7 | H7].
      -- rewrite H7. replace ((k - k)%nat) with 0%nat by lia. replace (k - (k - 1))%nat with (1)%nat by lia.
        simpl. repeat rewrite Rmult_1_r. unfold choose. assert (H8 : S k <? k = false). apply nltb_gt. lia.
        rewrite H8. replace (S k - k)%nat with 1%nat by lia. simpl. rewrite Rmult_1_r. rewrite plus_INR.
        rewrite mult_INR. nra.
      -- replace (n - k)%nat with (S (n - k) - 1)%nat by lia. rewrite Rmult_comm with (r2 := INR (fact (S (n - k) - 1))).
        rewrite fact_div' with (n := INR (fact n)).
        2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
        replace (S (n - k))%nat with (n - (k - 1))%nat at 2 by lia.
        rewrite Rmult_comm with (r2 := INR (fact k)).
        replace (INR (fact n) * INR k / (INR (fact k) * INR (fact (n - (k - 1)))) + INR (fact n) * INR (S (n - k)) / (INR (fact k) * INR (fact (n - (k - 1))))) with
        ((INR (fact n) * INR k + INR (fact n) * INR (S (n - k))) / (INR (fact k) * INR (fact (n - (k - 1))))).
        2 : { nra. }
        rewrite <- Rmult_plus_distr_l. rewrite <- plus_INR. replace (k + S (n - k))%nat with (S n)%nat by lia.
        replace (INR (fact n) * INR (S n)) with (INR (fact (S n))). 2 : { rewrite <- mult_INR. simpl. replace (fact n * S n)%nat with (fact n + n * fact n)%nat by lia.
        reflexivity. }
        unfold choose. assert (H8 : S n <? k = false). apply nltb_gt. lia. rewrite H8.
        replace (n - (k - 1))%nat with (S n - k)%nat by lia. reflexivity.
  Qed.

  Lemma binomial_recursion_R_2 : forall n k : nat,
    (k >= 1)%nat -> choose n (S k) = choose (S n) (S k) - n ∁ k.
  Proof.
    intros n k H1. rewrite binomial_recursion_R_1. 2 : { lia. } replace (S k - 1)%nat with k by lia. lra.
  Qed.

  Lemma n_choose_1 : forall (n : nat),
    n ∁ 1 = INR n.
  Proof.
    intro n. induction n as [| k IH].
    - compute. lra.
    - rewrite binomial_recursion_R_1; try lia. rewrite IH. replace (1 - 1)%nat with 0%nat by lia. rewrite n_choose_0. rewrite S_INR. lra.
  Qed.

  Lemma choose_natural : forall n k : nat,
    is_natural (n ∁ k).
  Proof.
    intros n k. assert ((n < k \/ n = k \/ n > k)%nat) as [H1 | [H1 | H1]] by lia.
    - exists 0%nat. rewrite k_gt_n_n_choose_k; try lia. reflexivity.
    - exists 1%nat. rewrite H1. rewrite n_choose_n. reflexivity.
    - generalize dependent k. induction n as [| n' IH].
      -- intros n H1. exists 0%nat. rewrite O_choose_n; lia.
      -- intros n H1. assert (n = 0 \/ n >= 1)%nat as [H2 | H2] by lia.
        + rewrite H2. exists 1%nat. rewrite n_choose_0. reflexivity.
        + assert (n' = n \/ n' > n)%nat as [H3 | H3] by lia.
          * rewrite binomial_recursion_R_1; try lia. rewrite H3 at 2. rewrite n_choose_n. specialize (IH (n - 1)%nat). destruct IH as [m H4]; try lia.
            exists (m+1)%nat. rewrite H4. rewrite plus_INR. reflexivity.
          * rewrite binomial_recursion_R_1; try lia. pose proof IH as IH2. specialize (IH n). specialize (IH2 (n-1)%nat). destruct IH as [m H4]; try lia.
            destruct IH2 as [m' H5]; try lia. exists (m + m')%nat. rewrite H4. rewrite H5. rewrite plus_INR. lra.
  Qed.

  Lemma pow_equ : forall (r: R) (a : nat),
    (a > 0)%nat -> r ^ a = r * r ^ (a - 1).
  Proof.
    intros r a H1. destruct a.
    - lia.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
  Qed.

  Theorem Binomial_Theorem_R : forall a b n,
    (a + b) ^ n = sum_f 0 n (fun i => (choose n i) * a ^ (n - i) * b ^ i).
  Proof.
    intros a b n. induction n as [| k IH].
    - compute; lra.
    - replace ((a + b) ^ (S k)) with ((a + b) * (a + b) ^ k) by (simpl; lra).
      rewrite Rmult_plus_distr_r. repeat rewrite IH. repeat rewrite r_mult_sum_f_i_n_f.
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * a) with (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * a) with (choose k x * (a ^ (k - x) * a) * b ^ x) by lra.
            replace (k - x + 1)%nat with (S (k - x))%nat by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * b) with (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1)).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * b) with (choose k x * a ^ (k - x) * (b ^ x * b)) by lra.
            replace (x + 1)%nat with (S x) by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (sum_f 0 k (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1))) with
      (sum_f 1 (k + 1) (fun i : nat => choose k (i-1) * a ^ (k - (i-1)) * b ^ (i))).
      2 : { rewrite sum_f_reindex' with (i := 0%nat) (n := k%nat) (s := 1%nat). simpl.
      set (f := fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i).
      set (g := fun x : nat => choose k (x - 1) * a ^ (k - (x - 1)) * b ^ (x - 1 + 1)).
      apply sum_f_equiv.
      - lia.
      - intros k0 H. unfold f, g. replace (k0 - 1 + 1)%nat with (k0) by lia. reflexivity. }
      destruct k as [| k'] eqn:Ek.
      -- compute. lra.
      -- rewrite sum_f_Si. 2 : { lia. }
        replace (S k' + 1)%nat with (S (k' + 1))%nat by lia.
        destruct k' as [| k''] eqn:Ek''.
        --- compute. lra.
        --- rewrite sum_f_i_Sn_f with (n := (S (k'' + 1))%nat). 2 : { lia. }
            repeat rewrite <- Ek. repeat replace ((S (k'' + 1))%nat) with (k)%nat by lia.
            replace (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + choose k 0 * a ^ (k - 0 + 1) * b ^ 0 +
            (sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k))
            with (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) +
            choose k 0 * a ^ (k - 0 + 1) * b ^ 0 + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k) by lra.
            rewrite sum_f_sum. assert (H2 : sum_f 1 k (fun x : nat => choose k x * a ^ (k - x + 1) * b ^ x + choose k (x - 1) * a ^ (k - (x - 1)) * b ^ x)
            = sum_f 1 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)).
            { apply sum_f_equiv. lia. intros k0 H2. replace (k - (k0 - 1))%nat with (k - k0 + 1)%nat by lia.
            rewrite Rmult_assoc. rewrite Rmult_assoc with (r1 := choose k (k0 - 1)) at 1.
            rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite binomial_recursion_R_1. 2 : { lia. } lra. }
            rewrite H2. rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_i_Sn_f. 2 : { lia. } replace (choose (S k) (S k)) with 1. 2 : { rewrite n_choose_n. auto. }
            replace (choose (S k) 0%nat) with 1. 2 : { rewrite n_choose_0. reflexivity. }
            repeat rewrite Rmult_1_l. replace (k - (S k - 1))%nat with 0%nat by lia. replace (S k - S k)%nat with 0%nat by lia.
            replace (b ^ 0) with 1 by auto. replace (a ^ 0) with 1 by auto. rewrite Rmult_1_l. repeat rewrite Rmult_1_r.
            replace (k - 0 + 1)%nat with (S k) by lia. replace (S k - 1)%nat with k%nat by lia. rewrite n_choose_n. rewrite Rmult_1_l. rewrite n_choose_0.
            rewrite Rmult_1_l. replace (sum_f 0 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)) with (sum_f 0 k (fun i : nat => choose (S k) i * a ^ (S k - i) * b ^ i)).
            2 : { apply sum_f_equiv. lia. intros k0 H3. replace (S k - k0)%nat with (k - k0 + 1)%nat by lia. reflexivity. }
            nra.
  Qed.
  
End Binomial_R.

Lemma Rdiv_natdiv : forall n1 n2 : nat,
  (n2 <> 0)%nat ->
  is_natural (INR (n1) / INR (n2)) -> Nat.divide n2 n1.
Proof.
  intros n1 n2 H1 [k H2]. exists k.  apply Rmult_eq_compat_r with (r := INR n2) in H2.
  field_simplify in H2. 2 : { apply not_0_INR; lia. } rewrite <- mult_INR in H2. apply INR_eq in H2. lia.
Qed.

Lemma fact_geq_1 : forall n : nat, (fact n >= 1)%nat.
Proof.
  induction n as [| k IH]; (simpl; lia).
Qed.

Lemma div_INR : forall n m : nat,
  (m <> 0)%nat -> (Nat.divide m n) -> INR (n / m) = INR n / INR m.
Proof.
  intros n m H1 [k H2]. rewrite H2. rewrite Nat.div_mul; auto. rewrite mult_INR. field. apply not_0_INR. lia.
Qed.

Lemma fact_div : forall (n k : nat),
  (k <= n)%nat -> Nat.divide (fact k * fact (n - k)) (fact n).
Proof.
  intros n k H1. apply Rdiv_natdiv. pose proof (fact_neq_0 k) as H2. pose proof (fact_neq_0 (n - k)) as H3. lia.
  rewrite mult_INR. replace (INR (fact n) / (INR (fact k) * INR (fact (n - k)))) with (Binomial_R.choose n k).
  2 : { unfold Binomial_R.choose. apply nltb_ge in H1. rewrite H1. reflexivity. }
  apply Binomial_R.choose_natural.
Qed.

Import Binomial_R.

Open Scope nat_scope.

Definition choose (n k : nat) : nat :=
if (n <? k) then 0 else
(fact n) / ((fact k) * (fact (n - k))).

Module Choose_Notations.

  Notation "n ∁ r" := (choose n r) (at level 10).

End Choose_Notations.

Import Choose_Notations.

Lemma Choose_N_eq_Choose_R : forall n k : nat,
  INR (n ∁ k) = Binomial_R.choose n k.
Proof.
  intros n k. unfold choose, Binomial_R.choose. destruct (n <? k) eqn:H1; try (simpl; lra).
  apply nltb_ge in H1. pose proof (fact_div n k H1) as H2. rewrite <- mult_INR. rewrite div_INR; try lia; try lra; auto.
  pose proof fact_neq_0 k as H3. pose proof fact_neq_0 (n - k) as H4. lia.
Qed.

Lemma n_choose_n : forall (n : nat),
  n ∁ n = 1.
Proof.
  intro n. pose proof Binomial_R.n_choose_n n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma Sn_choose_n : forall (n : nat),
  (S n) ∁ n = S n.
Proof.
  intro n. pose proof Binomial_R.Sn_choose_n n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma n_choose_0 : forall (n : nat),
  n ∁ 0 = 1.
Proof.
  intro n. pose proof Binomial_R.n_choose_0 n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. simpl. auto.
Qed.

Lemma O_choose_n : forall (n : nat),
  n <> 0 -> 0 ∁ n = 0.
Proof.
  intros n H1. pose proof Binomial_R.O_choose_n n H1 as H2. rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq. simpl. auto.
Qed.

Lemma n_lt_k_choose_k : forall n k : nat,
  n < k -> n ∁ k = 0.
Proof.
  intros n k H1. pose proof Binomial_R.k_gt_n_n_choose_k n k H1 as H2. rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq. auto.
Qed.

Lemma n_choose_1 : forall (n : nat),
  n ∁ 1 = n.
Proof.
  intro n. pose proof Binomial_R.n_choose_1 n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma n_choose_k_def : forall n k : nat,
  n >= k -> n ∁ k = fact n / (fact k * fact (n - k)).
Proof.
  intros n k H1. unfold choose. apply nltb_ge in H1. rewrite H1. reflexivity.
Qed.

Lemma binomial_recursion_1 : forall n k : nat,
  (n + 1) ∁ (k + 1) = n ∁ k + n ∁ (k + 1).
Proof.
  intros n k. assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
  - rewrite n_choose_0. repeat rewrite n_choose_1. lia.
  - pose proof Binomial_R.binomial_recursion_R_2 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
    rewrite plus_INR. replace (S k) with (k + 1)%nat in H2 by lia. replace (S n) with (n + 1)%nat in H2 by lia. lra.
Qed.

Lemma binomial_recursion_2 : forall n k : nat,
  (k >= 1) -> (n + 1) ∁ k = n ∁ k + n ∁ (k - 1).
Proof.
  intros n k H1. pose proof Binomial_R.binomial_recursion_R_1 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
  rewrite plus_INR. replace (S n) with (n + 1)%nat in H2 by lia. lra.
Qed.

Lemma choose_ge_0 : forall n k : nat,
  n ∁ k >= 0.
Proof.
  intros n k. induction n as [| n IH].
  - assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl. lia. rewrite O_choose_n; lia.
  - assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
    + rewrite n_choose_0. lia.
    + pose proof binomial_recursion_2 n k H1 as H2. lia.
Qed.

Lemma binomial_recursion_3 : forall n k : nat,
  n ∁ (k + 1) = (n + 1) ∁ (k + 1) - n ∁ k.
Proof.
  intros n k. assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
  - rewrite n_choose_0. repeat rewrite n_choose_1. lia.
  - pose proof Binomial_R.binomial_recursion_R_2 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
    replace (S k) with (k + 1)%nat in H2 by lia. replace (S n) with (n + 1)%nat in H2 by lia.
    assert (H3 : (n + 1) ∁ (k + 1) >= n ∁ k).
    { rewrite binomial_recursion_1. pose proof choose_ge_0 n k as H4. pose proof choose_ge_0 n (k + 1). lia. }
    rewrite minus_INR; try lia. lra.
Qed.

Lemma binomial_recursion_4 : forall n k : nat,
  n >= 1 -> k >= 1 -> n ∁ k = (n - 1) ∁ (k - 1) + (n - 1) ∁ k.
Proof.
  intros n k H1 H2. pose proof binomial_recursion_2 (n - 1) k H2 as H3.
  replace (n - 1 + 1) with n in H3 by lia. lia.
Qed.

Open Scope R_scope.

Theorem Binomial_Theorem : forall a b n,
  (a + b) ^ n = sum_f 0 n (fun i => INR (n ∁ i) * a ^ (n - i) * b ^ i).
Proof.
  intros a b n. pose proof Binomial_R.Binomial_Theorem_R a b n as H1. rewrite H1. apply sum_f_equiv. lia. intros i H2.
  rewrite <- Choose_N_eq_Choose_R. lra.
Qed.

Ltac simplify_nat_choose :=
  repeat match goal with
         | [ |- context[(?n ∁ ?k)] ] =>
           let C := eval compute in (choose n k) in
           change (n ∁ k) with C
         end.

Ltac simplify_power_expr :=
  repeat match goal with
  | |- context[?base ^ (?n - ?m)] =>
    let result := eval compute in (n - m)%nat in
    replace ((n - m)%nat) with (result) by (
      simpl; lia
    )
  end.

Ltac simplify_binomial_expansion :=
  rewrite Binomial_Theorem; repeat rewrite sum_f_i_Sn_f; try lia; rewrite sum_f_0_0; simplify_nat_choose; unfold INR; simplify_power_expr; field_simplify.


Module ChooseMemo.
  Import List ListNotations.

  Open Scope nat_scope.

  (* Define the type for the cache, where (n, k) is the key, and nat is the value *)
  Definition cache_t := list ((nat * nat) * nat).

  (* Function to look up a value from the cache, directly matching on the pair *)
  Fixpoint lookup_cache (n k : nat) (cache : cache_t) : option nat :=
    match cache with
    | [] => None
    | ((n', k'), value) :: rest =>
      if andb (n =? n') (k =? k') then Some value
      else lookup_cache n k rest
    end.

  (* Function to compute the binomial coefficient using memoization *)
  Fixpoint choose_memo (n k : nat) (cache : cache_t) : (nat * cache_t) :=
    if n <? k then (0, cache) else if n =? k then (1, cache) else if k =? 0 then (1, cache) else if (n =? 0) then (0, cache) else if k =? 1 then (n, cache) else
    match lookup_cache n k cache with
    | Some value => (value, cache)
    | None =>
      match n, k with
      | _, 0 =>
        let result := 1 in
        (result, (((n, k), result) :: cache))
      | 0, S _ =>
        let result := 0 in
        (result, (((n, k), result) :: cache))
      | S n', S k' =>
        if n =? k then
          let result := 1 in
          (result, (((n, k), result) :: cache))
        else
          let '(val1, cache1) := choose_memo n' k' cache in
          let '(val2, cache2) := choose_memo n' k cache1 in
          let result := val1 + val2 in
          (result, (((n, k), result) :: cache2))
      end
    end.

    Definition my_choose (n k : nat) : nat :=
      fst (choose_memo n k []).

    Lemma choose_memo_correct : forall n k cache,
      fst (choose_memo n k cache) = n ∁ k.
    Proof.
      intros n k cache. generalize dependent k. generalize dependent cache. induction n as [| n' IH]; intros cache k.
      - destruct k; simpl; reflexivity.
      - assert (k = 0 \/ k >= 1) as [H1 | H1] by lia.
        -- rewrite H1. simpl. rewrite n_choose_0. reflexivity.
        -- rewrite binomial_recursion_4; try lia. replace (S n' - 1) with n' by lia. simpl.
           assert (S n' < k \/ S n' >= k)%nat as [H2 | H2] by lia.
           * assert (S n' <? k = true) as H3. { apply Nat.ltb_lt. apply H2. } rewrite H3. simpl. repeat rewrite n_lt_k_choose_k; lia.
           * assert (S n' <? k = false) as H3. { apply Nat.ltb_ge. apply H2. } rewrite H3. destruct k; try lia. 
             assert (n' = k \/ n' > k)%nat as [H4 | H4] by lia.
             + assert (n' =? k = true) as H5. { apply Nat.eqb_eq. apply H4. } rewrite H5. simpl. rewrite H4. rewrite Nat.sub_0_r. 
               rewrite n_choose_n. rewrite n_lt_k_choose_k; lia.
             + assert (n' =? k = false) as H5. { apply Nat.eqb_neq. lia. } rewrite H5. simpl. assert (k = 0 \/ k > 0) as [H6 | H6] by lia.
               ** assert (k =? 0 = true) as H7. { apply Nat.eqb_eq. apply H6. } rewrite H7. simpl. rewrite Nat.sub_0_r. rewrite H6. rewrite n_choose_0. 
                  rewrite n_choose_1. lia.
               ** assert (k =? 0 = false) as H7. { apply Nat.eqb_neq. lia. } rewrite H7. destruct (lookup_cache) as [value |] eqn:H8.
                  --- simpl. rewrite Nat.sub_0_r. specialize (IH cache k). rewrite <- IH.
Admitted.

  Lemma my_choose_correct : forall n k,
    my_choose n k = n ∁ k.
  Proof.
    intros n k. generalize dependent k. induction n as [| n' IH]; intros k.
    - destruct k; simpl; reflexivity.
    - destruct k.
      -- rewrite n_choose_0. unfold my_choose, choose_memo. reflexivity.
      -- rewrite binomial_recursion_4; try lia. simpl. repeat rewrite Nat.sub_0_r. rewrite <- (IH k).
         rewrite <- (IH (S k)). unfold my_choose at 1. rewrite choose_memo_correct. rewrite binomial_recursion_4; try lia.
         simpl. repeat rewrite Nat.sub_0_r. rewrite <- IH. rewrite <- IH. reflexivity.
  Qed.
    
End ChooseMemo.

Compute (ChooseMemo.my_choose 40 5).

Open Scope nat_scope.