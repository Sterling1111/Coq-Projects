Require Import Reals Lra Lia ZArith FunctionalExtensionality List Classical Arith QArith.
Import ListNotations.
From Spivak Require Export Chapter1.

Module Znt := ZArith.Znumtheory.

Open Scope R_scope.

Theorem sum_n_nat : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i) = (INR n * (INR n + 1)) / 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_i : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_ii : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 3) = (sum_f 1 n (fun i => INR i)) ^ 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite sum_n_nat; auto. repeat rewrite S_INR. lra.  
Qed.

Lemma lemma_2_2_i : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => 2 * (INR i) - 1) = INR (n^2).
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (S k ^ 2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. repeat rewrite Nat.mul_1_r. lia. }
       replace (k^2 + 2 * k + 1)%nat with (k^2 + (2 * k + 1))%nat by lia. rewrite plus_INR.
       replace (2 * INR (S k) - 1) with (INR (2 * k + 1)).
       2 : { rewrite S_INR. repeat rewrite plus_INR. rewrite mult_INR. simpl. lra. }
       lra.
Qed.

Lemma lemma_2_2_ii : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => (2 * INR i - 1)^2) = INR n * (2 * INR n + 1) * (2 * INR n - 1) / 3.
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (INR (S k)) with (INR k + 1). 2 : { rewrite S_INR. auto. }
       field.
Qed.

Definition choose (n k : nat) : R :=
  if (n <? k) then 0 else
  (INR (fact n)) / (INR (fact k) * INR (fact (n - k))).

Lemma n_choose_n : forall (n : nat),
  choose n n = 1.
Proof.
  intro n. unfold choose. replace (n - n)%nat with 0%nat by lia.
  simpl. rewrite Rmult_1_r. rewrite Nat.ltb_irrefl.
  field. apply INR_fact_neq_0.
Qed.

Lemma n_choose_0 : forall (n : nat),
  choose n 0 = 1.
Proof.
  intro n. unfold choose. simpl. rewrite Nat.sub_0_r. rewrite Rmult_1_l.
  field. apply INR_fact_neq_0.
Qed.

Lemma O_choose_n : forall (n : nat),
  (n <> 0)%nat -> choose 0 n = 0.
Proof.
  intros n H1. unfold choose. simpl. destruct n; try lia; simpl. lra.
Qed.

Lemma k_gt_n_n_choose_k : forall n k : nat,
  (n < k)%nat -> choose n k = 0.
Proof.
  intros. assert (H2 : n <? k = true).
  { apply Nat.ltb_lt. apply H. }
  unfold choose. rewrite H2. reflexivity.
Qed.

Lemma nltb_gt : forall a b : nat, (a > b)%nat -> (a <? b) = false.
Proof.
  intros a b H. induction b.
  - auto.
  - unfold "<?". apply leb_correct_conv. lia.
Qed.

Lemma nltb_ge : forall a b : nat, (a >= b)%nat -> (a <? b) = false.
Proof.
  intros a b H. induction b.
  - auto.
  - unfold "<?". apply leb_correct_conv. lia.
Qed.

Lemma fact_div : forall m n k,
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

Lemma lemma_2_3_a : forall n k : nat,
  (k >= 1)%nat ->
  choose (S n) k = choose n (k - 1) + choose n k.
Proof.
  intros. assert (H2 : (S n < k \/ S n = k \/ S n > k)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
  - repeat rewrite k_gt_n_n_choose_k. lra. lia. lia. lia.
  - assert (H3 : (n = k - 1)%nat) by lia. rewrite <- H3. rewrite H2. repeat rewrite n_choose_n.
    rewrite k_gt_n_n_choose_k. lra. lia.
  - unfold choose at 2.
    assert (H3 : (n > k - 1)%nat) by lia. pose proof H3 as H4. apply nltb_gt in H4.
    rewrite H4. unfold choose at 2. assert (H5 : (n >= k)%nat) by lia. pose proof H5 as H6.
    apply nltb_ge in H6. rewrite H6. rewrite fact_div. 2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
    assert (H7: (n = k)%nat \/ (n > k)%nat) by lia. destruct H7 as [H7 | H7].
    -- rewrite H7. replace ((k - k)%nat) with 0%nat by lia. replace (k - (k - 1))%nat with (1)%nat by lia.
       simpl. repeat rewrite Rmult_1_r. unfold choose. assert (H8 : S k <? k = false). apply nltb_gt. lia.
       rewrite H8. replace (S k - k)%nat with 1%nat by lia. simpl. rewrite Rmult_1_r. rewrite plus_INR.
       rewrite mult_INR. nra.
    -- replace (n - k)%nat with (S (n - k) - 1)%nat by lia. rewrite Rmult_comm with (r2 := INR (fact (S (n - k) - 1))).
       rewrite fact_div with (n := INR (fact n)).
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

Lemma lemma_2_3' : forall n k : nat,
  (k >= 1)%nat -> choose n (S k) = choose (S n) (S k) - choose n k.
Proof.
  intros n k H1. rewrite lemma_2_3_a. 2 : { lia. } replace (S k - 1)%nat with k by lia. lra.
Qed.

Lemma n_choose_1 : forall (n : nat),
  choose n 1 = INR n.
Proof.
  intro n. induction n as [| k IH].
  - compute. lra.
  - rewrite lemma_2_3_a; try lia. rewrite IH. replace (1 - 1)%nat with 0%nat by lia. rewrite n_choose_0. rewrite S_INR. lra.
Qed.

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

Lemma lemma_2_3_b : forall n k : nat,
  is_natural (choose n k).
Proof.
  intros n k. assert ((n < k \/ n = k \/ n > k)%nat) as [H1 | [H1 | H1]] by lia.
  - exists 0%nat. rewrite k_gt_n_n_choose_k; try lia. reflexivity.
  - exists 1%nat. rewrite H1. rewrite n_choose_n. reflexivity.
  - generalize dependent k. induction n as [| n' IH].
    -- intros n H1. exists 0%nat. rewrite O_choose_n; lia.
    -- intros n H1. assert (n = 0 \/ n >= 1)%nat as [H2 | H2] by lia.
       + rewrite H2. exists 1%nat. rewrite n_choose_0. reflexivity.
       + assert (n' = n \/ n' > n)%nat as [H3 | H3] by lia.
         * rewrite lemma_2_3_a; try lia. rewrite H3 at 2. rewrite n_choose_n. specialize (IH (n - 1)%nat). destruct IH as [m H4]; try lia.
           exists (m+1)%nat. rewrite H4. rewrite plus_INR. reflexivity.
         * rewrite lemma_2_3_a; try lia. pose proof IH as IH2. specialize (IH n). specialize (IH2 (n-1)%nat). destruct IH as [m H4]; try lia.
           destruct IH2 as [m' H5]; try lia. exists (m + m')%nat. rewrite H4. rewrite H5. rewrite plus_INR. lra.
Qed.

Lemma lemma_2_3_d : forall a b n,
  (a + b) ^ n = sum_f 0 n (fun i => (choose n i) * a ^ (n - i) * b ^ i).
Proof.
  intros a b n. induction n as [| k IH].
  - compute; lra.
  - replace ((a + b) ^ (S k)) with ((a + b) * (a + b) ^ k) by (simpl; lra).
    rewrite Rmult_plus_distr_r. repeat rewrite IH. repeat rewrite r_mult_sum_f_i_n_f.
    replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * a) with (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i).
    2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * a) with (choose k x * (a ^ (k - x) * a) * b ^ x) by lra.
    rewrite pow_equ'. lra. }

    replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * b) with (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1)).
    2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * b) with (choose k x * a ^ (k - x) * (b ^ x * b)) by lra.
    rewrite pow_equ'. lra. } replace (sum_f 0 k (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1))) with
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
           rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite lemma_2_3_a. 2 : { lia. } lra. }
           rewrite H2. rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_i_Sn_f. 2 : { lia. } replace (choose (S k) (S k)) with 1. 2 : { rewrite n_choose_n. auto. }
           replace (choose (S k) 0%nat) with 1. 2 : { rewrite n_choose_0. reflexivity. }
           repeat rewrite Rmult_1_l. replace (k - (S k - 1))%nat with 0%nat by lia. replace (S k - S k)%nat with 0%nat by lia.
           replace (b ^ 0) with 1 by auto. replace (a ^ 0) with 1 by auto. rewrite Rmult_1_l. repeat rewrite Rmult_1_r.
           replace (k - 0 + 1)%nat with (S k) by lia. replace (S k - 1)%nat with k%nat by lia. rewrite n_choose_n. rewrite Rmult_1_l. rewrite n_choose_0.
           rewrite Rmult_1_l. replace (sum_f 0 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)) with (sum_f 0 k (fun i : nat => choose (S k) i * a ^ (S k - i) * b ^ i)).
           2 : { apply sum_f_equiv. lia. intros k0 H3. replace (S k - k0)%nat with (k - k0 + 1)%nat by lia. reflexivity. }
           nra.
Qed.

Lemma lemma_2_3_e_i : forall n,
  sum_f 0 n (fun j => choose n j) = 2 ^ n.
Proof.
  intros n. replace 2 with (1 + 1) by lra.
  rewrite lemma_2_3_d. apply sum_f_equiv; try lia.
  intros k H1. repeat rewrite pow1. lra.
Qed.

Lemma lemma_2_3_e_ii : forall n, 
  (n >= 1)%nat ->
    sum_f 0 n (fun j => (-1) ^ j * choose n j) = 0.
Proof.
  intros n H1. replace 0 with ((1 + -1)^n). 2 : { replace (1 + -1) with 0 by lra. rewrite Rpow_0; auto. }
  rewrite lemma_2_3_d. apply sum_f_equiv; try lia. intros k H2. rewrite pow1. lra.
Qed.

Lemma odd_spec_false : forall n : nat,
  Nat.odd n = false -> Nat.even n = true.
Proof.
  intros n H1. pose proof Nat.orb_even_odd n as H2. apply orb_prop in H2 as [H2 | H2]; auto.
  assert (true = false) as H3. rewrite <- H1, H2. reflexivity. inversion H3.
Qed.

Lemma even_spec_false : forall n : nat,
  Nat.even n = false -> Nat.odd n = true.
Proof.
  intros n H1. pose proof Nat.orb_even_odd n as H2. apply orb_prop in H2 as [H2 | H2]; auto.
  assert (true = false) as H3. rewrite <- H1, H2. reflexivity. inversion H3.
Qed.

Lemma lemma_2_3_e_iii : forall n,
  (n >= 1)%nat -> sum_f 0 n (fun l => if Nat.odd l then choose n l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.odd l then choose n l else 0) = sum_f 0 n (fun j => choose n j) - sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_minus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.odd k) eqn:H3.
    -- rewrite Nat.odd_spec in H3. destruct H3 as [m H3]. replace (2 * m + 1)%nat with (S (2 * m)) in H3 by lia. rewrite H3 at 3. rewrite pow_1_odd. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.even k = true) by (apply odd_spec_false; auto). rewrite Nat.even_spec in H5. destruct H5 as [m H5]. rewrite H5. rewrite pow_1_even. lra.
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rminus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.

Lemma lemma_2_3_e_iv : forall n,
  (n >= 1)%nat -> sum_f 0 n (fun l => if Nat.even l then choose n l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.even l then choose n l else 0) = sum_f 0 n (fun j => choose n j) + sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_plus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.even k) eqn:H3.
    -- rewrite Nat.even_spec in H3. destruct H3 as [m H3]. rewrite H3. rewrite pow_1_even. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.odd k = true) by (apply even_spec_false; auto). rewrite Nat.odd_spec in H5. destruct H5 as [m H5].
       replace (2 * m + 1)%nat with (S (2 * m)) in H5 by lia. rewrite H5 at 2. rewrite pow_1_odd. lra. 
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rplus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.

Lemma sum_f_l_n_0 : forall l n, (l <= n)%nat ->
  sum_f l n (fun i => 0) = 0.
Proof.
  intros l n H1. induction n as [| k IH].
  - destruct l. repeat rewrite sum_f_0_0. reflexivity. rewrite sum_f_Sn_n; try lia; try lra.
  - assert (l = S k \/ l <= k)%nat as [H2 | H2] by lia.
    -- rewrite <- H2. rewrite sum_f_n_n. reflexivity.
    -- rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. lra.
Qed.

Lemma lemma_2_4_a : forall l m n,
  sum_f 0 l (fun i => choose n i * choose m (l - i)) = choose (n + m) l.
Proof.
  intros l m n.  generalize dependent l. induction m as [| m' IHn].
  - induction n as [| n' IHm].
    -- intros l. destruct l.
      --- repeat rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
      --- rewrite sum_f_i_Sn_f; try lia. rewrite O_choose_n; try lia. rewrite Rmult_0_l. rewrite Rplus_0_r. rewrite O_choose_n; try lia.
          replace (fun i : nat => choose 0 i * choose 0 (S l - i)) with (fun i : nat => 0).
          { rewrite sum_f_l_n_0; try lia. reflexivity. } apply functional_extensionality. intros x. assert (x = 0 \/ x <> 0)%nat as [H1 | H1] by lia.
          rewrite H1. rewrite n_choose_0. rewrite O_choose_n. lra. lia. rewrite O_choose_n. lra. auto.
    -- intros l. destruct l.
      --- rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
      --- rewrite sum_f_i_Sn_f; try lia. replace (S l - S l)%nat with 0%nat by lia. rewrite n_choose_0.
          replace (sum_f 0 l (fun i : nat => choose (S n') i * choose 0 (S l - i))) with (sum_f 0 l (fun _ => 0)).
          2 : { apply sum_f_congruence; try lia. intros x H1. rewrite O_choose_n; try lia. lra. }
          rewrite sum_f_l_n_0; try lia. rewrite Nat.add_0_r. lra.
  - intros l. replace (n + S m')%nat with (S (n + m')) by lia. assert (l = 0 \/ l >= 1)%nat as [H1 | H1] by lia.
    -- rewrite H1. rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
    -- rewrite lemma_2_3_a; try lia. pose proof IHn as H2. pose proof IHn as H3.
       specialize (H2 l). specialize (H3 (l - 1)%nat). rewrite <- H2. rewrite <- H3.
       replace (sum_f 0 l (fun i : nat => choose n i * choose m' (l - i))) with (choose n l + sum_f 0 (l -1) (fun i : nat => choose n i * choose m' (l - i))).
       2 : { replace (l) with (S (l - 1)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (l - 1) - (S (l - 1)))%nat with 0%nat by lia. 
             rewrite n_choose_0. rewrite Rmult_1_r. replace (S (l - 1))%nat with l by lia. lra. }
       rewrite Rplus_comm. rewrite Rplus_assoc. rewrite sum_f_sum.
       replace (fun x : nat => choose n x * choose m' (l - x) + choose n x * choose m' (l - 1 - x)) with (fun x : nat => choose n x * (choose m' (l-x) + choose m' (l - 1- x))).
       2 : { apply functional_extensionality. intros x. lra. }
       replace (sum_f 0 (l - 1) (fun x : nat => choose n x * (choose m' (l - x) + choose m' (l - 1 - x)))) with (sum_f 0 (l-1) (fun x : nat => choose n x * choose (S m') (l - x))).
       2 : { apply sum_f_equiv. lia. intros x H4. rewrite Rplus_comm. replace (l - 1 - x)%nat with ((l-x) -1)%nat by lia. rewrite <- lemma_2_3_a. lra. lia. }
       replace (choose n l) with (choose n l * choose (S m') 0) by (rewrite n_choose_0; lra). rewrite Rplus_comm. replace (l - 1)%nat with (Nat.pred l) by lia.
       set (f := fun x : nat => choose n x * choose (S m') (l - x)). replace (choose n l * choose (S m') 0) with (f l).
       2 : { unfold f. replace (l - l)%nat with 0%nat by lia. lra. } rewrite <- sum_f_Pn; try lia. unfold f. apply sum_f_equiv. lia. intros x H5.
       assert (l - x = 0 \/ l - x >= 1)%nat as [H6 | H6] by lia.
       --- rewrite H6. repeat rewrite n_choose_0. repeat rewrite Rmult_1_r. lra.
       --- lra.
Qed.

Lemma n_choose_k_equiv : forall n k : nat,
  (k <= n)%nat -> choose n k = choose n (n - k).
Proof.
  intros n. induction n as [| n' IH].
  - destruct k; try lia. simpl. reflexivity.
  - intros k H1. assert (k = S n' \/ k <= n')%nat as [H2 | H2] by lia.
    -- rewrite H2. rewrite n_choose_n. replace (S n' - S n')%nat with 0%nat by lia. rewrite n_choose_0. reflexivity.
    -- assert (k = 0 \/ k >= 1)%nat as [H3 | H3] by lia.
       --- rewrite H3. rewrite n_choose_0. replace (S n' - 0)%nat with (S n')%nat by lia. rewrite n_choose_n. reflexivity.
       --- repeat rewrite lemma_2_3_a; try lia. replace (S n' - k - 1)%nat with (n' - k)%nat by lia. rewrite IH with (k := k); try lia.
           replace (S n' - k)%nat with (n' - (k - 1))%nat by lia. rewrite <- IH with (k := (k-1)%nat); try lia. lra.
Qed.

Lemma lemma_2_4_b : forall n : nat,
  sum_f 0 n (fun k : nat => (choose n k) ^ 2) = choose (2 * n)%nat n.
Proof.
  intros n. replace (2 * n)%nat with (n + n)%nat by lia. rewrite <- lemma_2_4_a with (m := n) (n := n).
  apply sum_f_equiv; try lia. intros k H1. rewrite n_choose_k_equiv; try lia. lra.
Qed.

Lemma lemma_2_5_a : forall n r,
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

Lemma lemma_2_5_b : forall n r,
  r <> 1 -> sum_f 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
Proof.
  intros n r H1. set (Sum := sum_f 0 n (fun i => r ^ i)).
  assert (H2 : r * Sum = sum_f 0 n (fun i => r ^ (S i))).
  { unfold Sum. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv. lia. intros k H2. simpl. lra. }
  assert (r = 0 \/ r <> 0) as [H3 | H3] by lra; assert (n = 0 \/ n > 0)%nat as [H4 | H4] by lia.
  - unfold Sum. rewrite H4. rewrite H3. rewrite sum_f_0_0. simpl. field.
  - unfold Sum. rewrite H3 in *. rewrite sum_f_Si; try lia. 
    replace (sum_f 1 n (fun i => 0 ^ i)) with (sum_f 1 n (fun i => 0)).
    2 : { apply sum_f_equiv. lia. intros k H5. destruct k. lia. simpl. lra. }
    rewrite sum_f_const. simpl. replace (n+1)%nat with (S n) by lia. simpl. lra.
  - unfold Sum. rewrite H4 in *. rewrite sum_f_0_0. simpl. field; lra.
  -  assert (H5 : r * Sum = sum_f 1 (n+1) (fun i : nat => r^i)).
    { rewrite sum_f_reindex with (s := 1%nat); try lia. simpl. replace (n + 1 - 1)%nat with n%nat by lia.
      replace (fun x : nat => r ^ (x + 1)) with (fun x : nat => r ^ (S x)). 
      2 : { apply functional_extensionality. intros x. replace (x + 1)%nat with (S x) by lia. reflexivity. }
      rewrite H2. apply sum_f_equiv; try lia. intros k H5. reflexivity.
    } assert (H6 : Sum - r * Sum = 1 - r^(n + 1)).
    { rewrite H5. unfold Sum. rewrite sum_f_Si_n_f with (i := 0%nat); try lia. replace (n+1)%nat with (S n) by lia.
      rewrite sum_f_i_Sn_f with (n := n); try lia. lra. }
    assert (H7 : Sum * (1 - r) = 1 - r ^ (n+1)) by nra. apply Rmult_eq_compat_r with (r := 1 / (1 - r)) in H7.
    field_simplify in H7; try nra. rewrite H7. field; nra.
Qed.

Lemma sum_f_1_n_fSi_minus_fi : forall n (f : nat -> R),
  (n >= 1)%nat -> sum_f 1 n (fun i => f (i+1)%nat - f i) = f (n+1)%nat - f 1%nat.
Proof.
  intros n f H1. induction n as [| n' IH]; try lia.
  assert (S n' = 1 \/ n' >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. 
    replace (S n') with (n' + 1)%nat by lia. lra.
Qed.

Lemma sum_f_1_n_fi_minus_fSi : forall n (f : nat -> R),
  (n >= 1)%nat -> sum_f 1 n (fun i => f i - f (i+1)%nat) = f 1%nat - f (n+1)%nat.
Proof.
  intros n f H1. induction n as [| n' IH]; try lia.
  assert (S n' = 1 \/ n' >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. 
    replace (S n') with (n' + 1)%nat by lia. lra.
Qed.

Lemma lemma_2_6_i : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 3) = INR n^4 / 4 + INR n^3 / 2 + INR n^2 / 4.
Proof.
  intros n H1. 
  assert (H2 : forall r, (r + 1)^4 - r^4 = 4 * r^3 + 6 * r^2 + 4 * r + 1) by (intros; nra).
  assert (H3 : sum_f 1 n (fun k : nat => INR (k + 1) ^ 4 - INR k ^ 4) = INR (n+1)^4 - 1).
  {
    set (f := fun x => INR x ^ 4). replace (INR (n + 1)^4) with (f (n+1)%nat) by reflexivity. replace 1 with (f 1%nat) by (compute; lra).
    apply sum_f_1_n_fSi_minus_fi with (n := n) (f := fun x => INR x ^ 4); lia.
  }
  assert (H4 : sum_f 1 n (fun k => 4 * INR k ^ 3 + 6 * INR k ^ 2 + 4 * INR k + 1) = 4 * sum_f 1 n (fun k => INR k^3) + 6 * sum_f 1 n (fun k => INR k^2) + 4 * sum_f 1 n (fun k => INR k) + INR n).
  {
    clear H3.
    induction n as [| n' IH]; try lia. assert (S n' = 1 \/ n' >= 1)%nat as [H3 | H3] by lia.
    - rewrite H3. compute. nra.
    - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. repeat rewrite S_INR. simpl. nra.
  }
  replace (sum_f 1 n (fun k : nat => INR k)) with (INR n * (INR n + 1) / 2) in H4 by (rewrite sum_n_nat; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 2)) with (INR n * (INR n + 1) * (2 * INR n + 1) / 6) in H4 by (rewrite lemma_2_1_i; auto).
  assert (H5 : (fun k : nat => INR (k + 1) ^ 4 - INR k ^ 4) = (fun k : nat => 4 * INR k ^ 3 + 6 * INR k ^ 2 + 4 * INR k + 1)).
  { apply functional_extensionality. intros x. specialize (H2 (INR x)). rewrite plus_INR. replace (INR 1) with 1 by reflexivity. apply H2. }
  rewrite <- H5 in H4. rewrite H3 in H4. replace (sum_f 1 n (fun i : nat => INR i ^ 3)) with 
  ((INR (n + 1) ^ 4 - 1 - 6 * (INR n * (INR n + 1) * (2 * INR n + 1) / 6) - 4 * (INR n * (INR n + 1) / 2) - INR n) / 4) by nra.
  rewrite plus_INR. simpl. nra.
Qed.

Lemma lemma_2_6_ii : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 4) = INR n^5 / 5 + INR n^4 / 2 + INR n^3 / 3 - INR n / 30.
Proof.
  intros n H1.
  assert (H2 : forall r, (r + 1)^5 - r^5 = 5 * r^4 + 10 * r^3 + 10 * r^2 + 5 * r + 1) by (intros; nra).
  assert (H3 : sum_f 1 n (fun k : nat => INR (k + 1) ^ 5 - INR k ^ 5) = INR (n+1)^5 - 1).
  { 
    set (f := fun x => INR x ^ 5). replace (INR (n + 1)^5) with (f (n+1)%nat) by reflexivity. replace 1 with (f 1%nat) by (compute; lra).
    apply sum_f_1_n_fSi_minus_fi with (n := n) (f := fun x => INR x ^ 5); lia.
  }
  assert (H4 : sum_f 1 n (fun k => 5 * INR k ^ 4 + 10 * INR k ^ 3 + 10 * INR k ^ 2 + 5 * INR k + 1) = 5 * sum_f 1 n (fun k => INR k^4) + 10 * sum_f 1 n (fun k => INR k^3) + 10 * sum_f 1 n (fun k => INR k^2) + 5 * sum_f 1 n (fun k => INR k) + INR n).
  {
    clear H3.
    induction n as [| n' IH]; try lia. assert (S n' = 1 \/ n' >= 1)%nat as [H3 | H3] by lia.
    - rewrite H3. compute. nra.
    - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. repeat rewrite S_INR. simpl. nra.
  }
  replace (sum_f 1 n (fun k : nat => INR k)) with (INR n * (INR n + 1) / 2) in H4 by (rewrite sum_n_nat; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 2)) with (INR n * (INR n + 1) * (2 * INR n + 1) / 6) in H4 by (rewrite lemma_2_1_i; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 3)) with (INR n^4 / 4 + INR n^3 / 2 + INR n^2 / 4) in H4 by (rewrite lemma_2_6_i; auto).
  assert (H5 : (fun k : nat => INR (k + 1) ^ 5 - INR k ^ 5) = (fun k : nat => 5 * INR k ^ 4 + 10 * INR k ^ 3 + 10 * INR k ^ 2 + 5 * INR k + 1)).
  { apply functional_extensionality. intros x. specialize (H2 (INR x)). rewrite plus_INR. replace (INR 1) with 1 by reflexivity. apply H2. }
  rewrite <- H5 in H4. rewrite H3 in H4. replace (sum_f 1 n (fun i : nat => INR i ^ 4)) with 
  ((INR (n + 1) ^ 5 - 1 - 10 * (INR n ^ 4 / 4 + INR n ^ 3 / 2 + INR n ^ 2 / 4) - (10 * (INR n * (INR n + 1) * (2 * INR n + 1) / 6)) - 5 * (INR n * (INR n + 1) / 2) - INR n) / 5) by nra.
  rewrite plus_INR. simpl. nra.
Qed.

Lemma lemma_2_6_iii : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => 1 / INR (i * (i + 1))) = 1 - 1 / INR (n + 1).
Proof.
  intros n H1.
  set (f := fun x => 1 / INR x). replace 1 with (f 1%nat) at 1 by (compute; lra).
  replace (1 / INR (n + 1)) with (f (n + 1)%nat) at 1 by reflexivity. rewrite <- sum_f_1_n_fi_minus_fSi with (n := n) (f := f); try lia.
  apply sum_f_equiv; try lia. intros k H2. unfold f. rewrite mult_INR. repeat rewrite plus_INR. simpl. field. split.
  - rewrite <- INR_1. rewrite <- plus_INR. apply not_0_INR. lia.
  - apply not_0_INR. lia.
Qed.

Lemma lemma_2_6_iv : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR (2 * i + 1) / INR (i^2 * (i + 1)^2)) = 1 - 1 / (INR (n + 1)^2).
Proof.
  intros n H1.
  set (f := fun x => 1 / INR (x^2)). replace 1 with (f 1%nat) at 1 by (compute; lra).
  replace (1 / INR (n + 1)^2) with (f (n + 1)%nat). 2 : { unfold f. rewrite pow_INR. reflexivity. } 
  rewrite <- sum_f_1_n_fi_minus_fSi with (n := n) (f := f); try lia. apply sum_f_equiv; try lia. intros k H2.
  unfold f. simpl. repeat rewrite mult_INR. repeat rewrite plus_INR. simpl. field. split.
  - rewrite <- INR_1. rewrite <- plus_INR. apply not_0_INR. lia.
  - apply not_0_INR. lia.
Qed.

Open Scope nat_scope. 

Lemma lemma_2_8 : forall n : nat,
  Nat.Even n \/ Nat.Odd n.
Proof.
  intros n. induction n as [| k IH].
  - left. unfold Nat.Even. exists 0. lia.
  - destruct IH as [IH | IH].
    -- right. unfold Nat.Odd in *. destruct IH as [k0 H]. exists (k0). lia.
    -- left. unfold Nat.Even in *. destruct IH as [k0 H]. exists (S k0). lia.
Qed.

Lemma lemma_2_8' : forall z : Z,
  Z.Even z \/ Z.Odd z.
Proof.
  intros z. rewrite <- Zeven_equiv. rewrite <- Zodd_equiv.
  destruct (Zeven_odd_dec z) as [H | H].
  - auto.
  - auto.
Qed.

Lemma lemma_2_9 : forall (A : nat -> Prop) (n0 : nat),
  (A n0 /\ (forall k : nat, A k -> A (S k))) ->
  forall n : nat, n >= n0 -> A n.
Proof.
  intros A n0 [H1 H2] n H3.
  induction n as [| k IH].
  - inversion H3. rewrite H in H1. apply H1.
  - assert (H4 : n0 = S k \/ n0 < S k) by lia. destruct H4 as [H4 | H4].
    -- rewrite H4 in H1. apply H1.
    -- apply H2. apply IH. lia.
Qed.

Definition induction_nat := forall P : nat -> Prop,
  (P 0 /\ (forall k : nat, P k -> P (S k))) -> forall n, P n.

Definition strong_induction_nat := forall P : nat -> Prop,
  (forall m, (forall k : nat, k < m -> P k) -> P m) -> forall n, P n.

Definition well_ordering_nat := forall E : nat -> Prop,
  (exists x, E x) -> (exists n, E n /\ forall m, E m -> (n <= m)).

Lemma induction_imp_induction_nat : induction_nat.
Proof.
  unfold induction_nat. intros P [H_base H_ind] n.
  induction n as [| k IH].
  - apply H_base.
  - apply H_ind. apply IH.
Qed.

Lemma lemma_2_10 : well_ordering_nat -> induction_nat.
Proof.
  unfold well_ordering_nat, induction_nat. intros well_ordering_nat P [Hbase H_inductive] n.
  set (E := fun m => ~ P m).
  specialize (well_ordering_nat E). assert (H1 : forall n : nat, E n -> False).
  - intros x H1. assert (H3 : exists x, E x) by (exists x; auto). apply well_ordering_nat in H3.
    destruct H3 as [least_elem_E H3]. destruct H3 as [H3 H4]. specialize (H_inductive (least_elem_E - 1)).
    destruct least_elem_E as [| least_elem_E'].
    -- apply H3. apply Hbase.
    -- specialize (H4 least_elem_E'). assert (H5 : S least_elem_E' <= least_elem_E' -> False) by lia.
       assert (H6 : ~(E least_elem_E')) by tauto. unfold E in H6. simpl in *. rewrite Nat.sub_0_r in *.
       apply NNPP in H6. apply H_inductive in H6. apply H3. apply H6.
  - specialize (H1 n). unfold E in H1. apply NNPP in H1. apply H1.
Qed.

Lemma lemma_2_11 : induction_nat -> strong_induction_nat.
Proof.
  unfold induction_nat, strong_induction_nat. intros induction_nat P H1 n.
  assert (H2 : forall k, k <= n -> P k).
  - apply induction_nat with (n := n). split.
    -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
    -- intros k Hk. intros k' Hk'. apply H1. intros k'' Hk''. apply Hk. lia.
  - apply H2. lia.
Qed.

Lemma strong_induction_N : strong_induction_nat.
Proof.
  apply lemma_2_11. apply induction_imp_induction_nat.
Qed.

Ltac strong_induction n :=
  apply (strong_induction_N (fun n => _));
  let n := fresh n in
  intros n IH.

Open Scope R_scope.

Lemma exist_R_plus_eq_l : forall (r r1 : R) (f : list R -> R),
  (exists l, r1 = (f l)) -> (exists l, r + r1 = r + f l).
Proof.
  intros. destruct H as [l H]. exists l. lra.
Qed.

Lemma lemma_2_7 : forall n p,
  (n >= 1)%nat -> (p >= 1)%nat ->
    exists l : list R,
      sum_f 1 n (fun i => INR i ^ p) = INR n ^ (p + 1) / INR (p + 1) + sum_f 0 (p-1) (fun i => nth i l 0 * INR n ^ (p-i)).
Proof.
  intros n p H1 H2. apply strong_induction_N with (n := p).
  intros m IH. assert (m = 0 \/ m = 1 \/ m >= 2)%nat as [H3 | [H3 | H3]] by lia.
  - rewrite H3. simpl. rewrite sum_f_const. exists [0]. rewrite sum_f_0_0. simpl. rewrite plus_INR.
    rewrite minus_INR; try lia. simpl. lra.
  - rewrite H3. replace ((fun i => INR i ^ 1)) with (fun i => INR i) by (apply functional_extensionality; intros; lra).
    rewrite sum_n_nat; auto. exists [1/2]. rewrite sum_f_0_0. simpl. lra.
  - assert (H4 : forall k, (INR k + 1)^(m+1) - (INR k)^(m+1) = sum_f 2 (m+1) (fun i => choose (m+1) i * (INR k)^(m+1-i)) + INR (m + 1) * INR k ^ m).
    {
      intros k. rewrite lemma_2_3_d. rewrite sum_f_Si; try lia. rewrite n_choose_0. simpl. rewrite Rmult_1_r. rewrite Rmult_1_l. 
      replace (m+1-0)%nat with (m+1)%nat by lia. unfold Rminus. rewrite Rplus_assoc.
      field_simplify. rewrite sum_f_Si; try lia. rewrite n_choose_1. replace (m + 1 - 1)%nat with m by lia. replace (INR (m + 1) * INR k ^ m * 1 ^ 1) with (INR (m + 1) * INR k ^ m) by (simpl; lra).
        apply Rplus_eq_compat_r. apply sum_f_equiv; try lia. intros k2 H5. rewrite pow1. rewrite Rmult_1_r. reflexivity. 
    }
    assert (H5 : sum_f 1 n (fun i => (INR i + 1) ^ (m + 1) - INR i ^ (m + 1)) = (INR n + 1)^(m+1) - 1).
    {
      set (f := fun x => INR x ^ (m+1)). replace ((INR n + 1) ^ (m + 1)) with (f (n+1)%nat).
      2 : { unfold f. rewrite plus_INR. reflexivity. }
      replace 1 with (f 1%nat).
      2 : { unfold f. simpl. rewrite pow1. reflexivity. }
      rewrite <- sum_f_1_n_fSi_minus_fi with (n := n) (f := f); try lia. apply sum_f_equiv; try lia. intros k H5.
      unfold f. rewrite plus_INR. simpl. rewrite pow1. reflexivity.
    }
    assert (H6 : sum_f 1 n (fun i => (INR i + 1)^(m+1) - (INR i)^(m+1)) = sum_f 1 n (fun i => sum_f 2 (m+1) (fun j => choose (m+1) j * (INR i)^(m+1-j)) + INR (m + 1) * INR i ^ m)).
    { apply sum_f_equiv; try lia. intros k H6. specialize (H4 k). rewrite <- H4. lra. } rewrite H5 in H6. rewrite <- sum_f_plus in H6; try lia. rewrite <- r_mult_sum_f_i_n_f_l in H6.
    rewrite Rplus_comm in H6. rewrite lemma_2_3_d in H6. replace ((fun i : nat => choose (m + 1) i * 1 ^ (m + 1 - i) * INR n ^ i)) with 
    (fun i : nat => choose (m + 1) i * INR n ^ i) in H6. 2 : { apply functional_extensionality. intros. rewrite pow1. lra. }
    rewrite sum_f_Si in H6; try lia. rewrite n_choose_0 in H6. simpl in H6. rewrite Rmult_1_r in H6. field_simplify in H6.
    replace (m + 1)%nat with (S m) in H6 at 1 by lia. rewrite sum_f_i_Sn_f in H6; try lia. replace (S m) with (m + 1)%nat in H6 by lia.
    rewrite n_choose_n in H6. field_simplify in H6. rewrite sum_swap in H6; try lia. replace (fun j : nat => sum_f 1 n (fun i : nat => choose (m + 1) j * INR i ^ (m + 1 - j))) with 
    (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) in H6. 2 : { apply functional_extensionality. intros. apply r_mult_sum_f_i_n_f_l. }
    assert (H7 : INR (m + 1) * sum_f 1 n (fun i : nat => INR i ^ m) = INR n ^ (m + 1) + sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) by nra.
    assert (H8 : sum_f 1 n (fun i : nat => INR i ^ (m)) = INR n ^ (m + 1) / INR (m + 1) + (sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) / INR (m + 1) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1))). 
    { apply Rmult_eq_reg_l with (r := INR (m + 1)). rewrite H7. field. apply not_0_INR. lia. apply not_0_INR. lia. }
    rewrite H8.  apply exist_R_plus_eq_l. 
Abort.

Close Scope R_scope.

Lemma well_ordering_nat_contrapositive : forall E : nat -> Prop,
  (~(exists m, E m /\ forall k, E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E H.
  set (E' := fun n => ~ E n).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split. apply H2. intros k H3. lia. }
  assert (H2: forall n, E' n).
  {
    strong_induction n. destruct n.
    - unfold E'. unfold not. apply H0.
    - assert (E (S n) -> False).
      { intros H3. apply H. exists (S n). split. apply H3. intros k H4.
        specialize (IH k). assert (E' k -> False). unfold E'.
        unfold not. intros H5. apply H5. apply H4. assert (k < S n -> False) by auto.
        lia.
      }
      unfold E'. unfold not. apply H1.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply H3.
Qed.

Theorem well_ordering_N : well_ordering_nat.
Proof.
  intros E.
  assert (H :
    ~(exists m, E m /\ forall k, E k -> m <= k) ->
      ~(exists n, E n)) by apply well_ordering_nat_contrapositive.

  intros [x Ex].
  destruct (classic (exists m, E m /\ forall k, E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex.
Qed.

Close Scope nat_scope.

Open Scope Z_scope.

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

Theorem QRTE : forall a d : Z,
  (d >= 1) -> exists q r : Z, a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hb.
  set (S z := exists t : Z, z = a - t * d /\ z >= 0).
  assert (Ht : exists t : Z, S t).
  {
    destruct (Z_le_dec 0 a) as [Ha | Ha].
    - exists a. unfold S. exists 0. split. simpl. rewrite Z.sub_0_r. reflexivity. apply Z.le_ge. apply Ha.
    - unfold not in Ha. exists (a * (1 - d)). unfold S. exists a. split. lia.
      assert (1 - d <= 0) by lia. destruct (Z.eq_dec (1 - d) 0) as [H2 | H2].
      -- lia.
      -- assert (H3 : 1 - d < 0) by lia. assert (H4 : a < 0) by lia.
         assert (H5 : forall z : Z, z > 0 -> z >= 0) by lia. apply H5.
         apply Z.lt_gt. apply Z.mul_neg_neg. lia. lia.
  }
  apply well_ordering_Z in Ht.
  - destruct Ht as [r Ht]. destruct Ht as [Ht Ht'].
    unfold S in Ht. destruct Ht as [t Ht]. destruct Ht as [Ht Ht''].
    exists t. exists r. split. lia. destruct (classic (r < d)) as [H1 | H1].
    -- lia.
    -- assert (H2 : r >= d) by lia. assert (H3 : a - t * d >= d) by lia.
       assert (H4 : a - d * (t - 1) >= 0) by lia.  assert (H5 : r - d >= 0) by lia.
       assert (H6 : S (r - d)). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H7 : S (a - d * (t + 1))). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H8 : r <= r - d). { apply Ht'. lia. apply H6. } lia.
    - intros z. unfold S. intros H. destruct H as [t H]. lia.
Qed.

Theorem QRTU : forall a d q1 q2 r1 r2 : Z,
  (d >= 1) /\  a = d * q1 + r1 /\ a = d * q2 + r2 /\ 0 <= r1 < d /\ 0 <= r2 < d
  -> q1 = q2 /\ r1 = r2.
Proof.
  intros a d q1 q2 r1 r2 [H1 [H2 [H3 [H4 H5]]]].
  assert (H: q1 = q2).
  {
    assert (H6 : q1 * d + r1 = q2 * d + r2) by lia.
    assert (H7 : (q1 - q2) * d = r2 - r1) by lia.
    assert (H8 : -d < -r1 <= 0) by lia.
    assert (H9 : 0 <= r2 < d) by lia.
    assert (H10 : -d < r2 - r1 < d) by lia.
    assert (H11 : -d < (q1 - q2) * d < d) by lia.
    destruct H11 as [H11 H12].
    assert (H13 : -1 < q1 - q2).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. }
    assert (H14 : q1 - q2 < 1).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. }
    lia.
  }
  split.
  - apply H.
  - lia.
Qed.

Theorem QRT : forall a d : Z,
  d >= 1 ->
  exists! p : (Z * Z), let (q, r) := p in a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hd.
  apply unique_existence with (P := fun p : (Z * Z) => let (q, r) := p in a = d * q + r /\ 0 <= r < d).
  split.
  - destruct (QRTE a d Hd) as [q [r [H1 H2]]].
    exists (q, r). auto.
  - intros [q1 r1] [q2 r2] [H1a H1b] [H2a H2b].
    assert (H3 : q1 = q2 /\ r1 = r2) by (apply QRTU with (a := a) (d := d); auto).
    destruct H3 as [H3a H3b]. rewrite H3a. rewrite H3b. reflexivity.
Qed.

Lemma gcd_0 : forall a b : Z, Z.gcd a b = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b H1. split.
  - pose proof Z.gcd_divide_l a b as H2. destruct H2 as [k H2]. lia.
  - pose proof Z.gcd_divide_r a b as H2. destruct H2 as [k H2]. lia.
Qed.

Lemma gcd_gt_0 : forall a b : Z, a <> 0 -> b <> 0 -> Z.gcd a b > 0.
Proof.
  intros a b H1 H2. pose proof Z.gcd_nonneg a b. assert (Z.gcd a b = 0 \/ Z.gcd a b > 0) as [H3 | H3] by lia.
  - apply gcd_0 in H3. lia.
  - auto.
Qed.

Definition rational (r : R) : Prop :=
  exists z1 z2 : Z, (r = (IZR z1) / (IZR z2))%R.

Definition irrational (r : R) : Prop :=
  ~ rational r.

Lemma rational_representation : forall r z1 z2,
  z1 <> 0 -> z2 <> 0 ->
  (r = IZR z1 / IZR z2)%R -> exists z1' z2',
    ((r = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2'))).
Proof.
  intros r z1 z2 H1 H2 H3. exists (z1 / Z.gcd z1 z2). exists (z2 / Z.gcd z1 z2). split.
  - rewrite H3. pose proof Z.gcd_divide_r z1 z2 as H4. pose proof Z.gcd_divide_l z1 z2 as H5.
    unfold Z.divide in H4. unfold Z.divide in H5. destruct H4 as [k1 H4]. destruct H5 as [k2 H5].
    assert (Z.gcd z1 z2 <> 0) as H6 by lia.
    assert (H7 : Z.gcd z1 z2 > 0). { pose proof Z.gcd_nonneg z1 z2. lia. }
    replace (z1 / Z.gcd z1 z2) with (k2). 2 : { rewrite H5 at 1. rewrite Z_div_mult. reflexivity. lia. }
    replace (z2 / Z.gcd z1 z2) with (k1). 2 : { rewrite H4 at 1. rewrite Z_div_mult. reflexivity. lia. }
    rewrite H4. rewrite H5 at 1. repeat rewrite mult_IZR.
    replace ((IZR k2 * IZR (Z.gcd z1 z2) / (IZR k1 * IZR (Z.gcd z1 z2)))%R) with
            ( IZR k2 / IZR k1 * (IZR (Z.gcd z1 z2) / IZR (Z.gcd z1 z2)))%R.
    2 : { field. split. apply not_0_IZR. auto. apply not_0_IZR. lia. }
    rewrite Rdiv_diag. 2 : { apply not_0_IZR. lia. } nra.
  - intros x H4. apply not_and_or. intros [[a H5] [b H6]]. pose proof Z.gcd_divide_l z1 z2 as [c H7].
    pose proof Z.gcd_divide_r z1 z2 as [d H8]. rewrite H7 in H5 at 1. rewrite H8 in H6 at 1.
    rewrite Z_div_mult in H5 by (apply gcd_gt_0; auto). rewrite Z_div_mult in H6 by (apply gcd_gt_0; auto).
    rewrite H5 in H7. rewrite H6 in H8. assert (H9 : Z.divide (x * Z.gcd z1 z2) z1). { rewrite H7 at 2. exists (a). lia. }
    assert (H10 : Z.divide (x * Z.gcd z1 z2) z2). { exists (b). lia. } pose proof Z.gcd_greatest z1 z2 (x * Z.gcd z1 z2) as H11.
    apply H11 in H9. 2 : { auto. } unfold Z.divide in H9. destruct H9 as [k H9]. assert (Z.gcd z1 z2 > 0) as H12 by (apply gcd_gt_0; auto).
    assert (k < 0 \/ k = 0 \/ k > 0) as [H13 | [H13 | H13]] by lia.
    -- nia.
    -- nia.
    -- assert (H14 : k * x * Z.gcd z1 z2 > Z.gcd z1 z2). { rewrite <- Zmult_1_l. apply Zmult_gt_compat_r. lia. lia. }
       nia.
Qed.

Lemma even_pow2 : forall z,
  Z.Even (z * z) -> Z.Even z.
Proof.
  intros z H. pose proof lemma_2_8' z as [H1 | H1].
  - auto.
  - destruct H1 as [k H1]. destruct H as [k' H]. nia.
Qed.

Lemma sqrt_rational_neq_0 : forall r z1 z2,
  (r > 0)%R -> sqrt r = (IZR z1 / IZR z2)%R -> (z1 <> 0 /\ z2 <> 0).
Proof.
  intros r z1 z2 H1 H2. split.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_l in H2. pose proof sqrt_lt_R0 r. nra.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_r in H2. pose proof sqrt_lt_R0 r. nra.
Qed.

Lemma sqrt_2_irrational : irrational (sqrt 2).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 2 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 2 * sqrt 2 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6.
  apply eq_IZR in H6. assert (H11 : Z.Even (z1' * z1')). { exists (z2' * z2'). lia. }
  apply even_pow2 in H11. destruct H11 as [k1 H11]. assert (H12 : Z.Even (z2' * z2')). { exists (k1 * k1). nia. }
  apply even_pow2 in H12. destruct H12 as [k2 H12]. specialize (H5 2). destruct H5 as [H5 | H5].
  { lia. } { apply H5. unfold Z.divide. exists (k1). lia. } { apply H5. unfold Z.divide. exists (k2). lia. }
Qed.

Lemma lemma_2_12_a : forall a b,
  rational a -> rational b -> rational (a + b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert ((a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R) as [H3 | [H3 | H3]] by lra.
  - exists z3. exists z4. nra.
  - exists z1. exists z2. nra.
  - assert (H4 : forall x y z, (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0).
    { intros x y z [H4 H5]. assert (z <> 0 \/ z = 0) as [H6 | H6] by lia. auto. rewrite H6 in H5. rewrite Rdiv_0_r in H5. nra. }
    assert (H5 : z2 <> 0 /\ z4 <> 0). { split. apply H4 with (x := a) (y := z1). tauto. apply H4 with (x := b) (y := z3). tauto. }
    unfold rational. exists (z1 * z4 + z3 * z2). exists (z2 * z4). rewrite H1. rewrite H2. rewrite plus_IZR.
    repeat rewrite mult_IZR. field; split; apply not_0_IZR; lia.
Qed.

Lemma lemma_2_12_a' : forall a,
  irrational a -> exists b, irrational b /\ rational (a + b).
Proof.
  intros a H1. exists (-a)%R. split.
  - intros [z1 [z2 H2]]. apply H1. exists (-z1), z2. replace (-z1) with (-1 * z1) by lia. rewrite mult_IZR. lra.
  - exists 0, 1. nra.
Qed.

Lemma lemma_2_12_b : forall b,
  irrational b -> exists a, rational a /\ rational (a * b).
Proof.
  intros a H1. exists 0%R. split; exists 0, 1; nra.
Qed.

Lemma x_neq_0_IZR_den_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0. 
Proof.
  intros x y z [H1 H2]. assert (z <> 0 \/ z = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_r in H2. nra.
Qed.

Lemma x_neq_0_IZR_num_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> y <> 0.
Proof.
  intros x y z [H1 H2]. assert (y <> 0 \/ y = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_l in H2. nra.
Qed.

Lemma mult_rational : forall a b,
  rational a -> rational b -> rational (a * b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert (a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R as [H3 | [H3 | [H3 H4]]] by lra.
  - exists 0, 1. nra.
  - exists 0, 1. nra.
  - exists (z1 * z3). exists (z2 * z4). rewrite H1. rewrite H2. repeat rewrite mult_IZR. field.
    split; apply not_0_IZR.
    -- apply x_neq_0_IZR_den_neq_0 with (x := b) (y := z3) (z := z4). auto.
    -- apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto.
Qed.

Lemma lemma_2_12_b' : forall a b,
  a <> 0%R -> rational a -> irrational b -> irrational (a * b).
Proof.
  intros a b H1 H2 H3. assert (irrational (a * b) \/ rational (a * b)) as [H4 | H4].
  { unfold irrational. tauto. } auto.
  destruct H2 as [z1 [z2 H2]]. assert (H5 : z1 <> 0). { apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H6 : z2 <> 0). { apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H7 : rational (/ a)) by (exists z2, z1; rewrite H2; field; split; apply not_0_IZR; lia).
  assert (H8 : b <> 0%R) by (intros H8; apply H3; exists 0, 1; nra).
  assert (H9 : / a <> 0%R) by (apply Rinv_neq_0_compat; auto).
  assert (H10 : rational b).
  { replace b with (a * b / a)%R by (field; auto). apply mult_rational; auto. }
  unfold irrational in H3. tauto.
Qed.

Lemma lemma_2_12_a'' : exists a b, irrational (a + b).
Proof.
  exists (sqrt 2), (sqrt 2). replace (sqrt 2 + sqrt 2)%R with (2 * sqrt 2)%R by lra. apply lemma_2_12_b' with (a := 2%R) (b := (sqrt 2)%R).
  - lra.
  - exists 2, 1. nra.
  - apply sqrt_2_irrational.
Qed.

Lemma lemma_2_12_c : exists a,
  irrational (a^2) /\ rational (a^4).
Proof.
  exists (sqrt (sqrt 2)). split.
  - simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } apply sqrt_2_irrational.
  - exists 2, 1. simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. }
    rewrite <- Rmult_assoc. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } 
    rewrite sqrt_sqrt; nra.
Qed.

Lemma lemma_2_12_d : exists a b,
  irrational a -> irrational b -> rational (a * b) /\ rational (a + b).
Proof.
  exists (sqrt 2), (-(sqrt 2))%R. intros H1 H2. split.
  - exists (-2), 1. replace (sqrt 2 * - sqrt 2)%R with (- (sqrt 2 * sqrt 2))%R by lra. rewrite sqrt_sqrt; lra.
  - exists 0, 1. lra.
Qed.

Ltac zforms :=
  match goal with
  | [ |- exists _, ?n = ?num * _ \/ _ ] =>
      destruct (QRTE n num) as [q [r Hqr]];
      try exists q;
      lia
  | _ => fail "Goal does not match expected pattern"
  end.

Lemma ksqr_div_3_k_div_3 : forall k,
  Z.divide 3 (k^2) -> Z.divide 3 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 3*p \/ k = 3*p+1 \/ k = 3*p+2) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_a : irrational (sqrt 3).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 3 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 3 * sqrt 3 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 3 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 3 z1') as H12 by (apply ksqr_div_3_k_div_3; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 3 * (3 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 3 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 3 z2') as H17 by (apply ksqr_div_3_k_div_3; auto). specialize (H5 3). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma ksqr_div_3_k_div_5 : forall k,
  Z.divide 5 (k^2) -> Z.divide 5 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 5*p \/ k = 5*p+1 \/ k = 5*p+2 \/ k = 5*p+3 \/ k = 5*p+4) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_a' : irrational (sqrt 5).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 5%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 5 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 5 * sqrt 5 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 5%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 5 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 5 z1') as H12 by (apply ksqr_div_3_k_div_5; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 5 * (5 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 5 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 5 z2') as H17 by (apply ksqr_div_3_k_div_5; auto). specialize (H5 5). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma ksqr_div_6_k_div_6 : forall k,
  Z.divide 6 (k^2) -> Z.divide 6 k.
Proof.
  intros k [a H1]; unfold Z.divide;
  assert (exists p, k=6*p\/k=6*p+1\/k=6*p+2\/k=6*p+3\/k=6*p+4\/k=6*p+5) as [p H2] by zforms;
  exists p; lia.
Qed.

Lemma lemma_2_13_a'' : irrational (sqrt 6).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 6%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 6 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 6 * sqrt 6 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 6%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 6 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 6 z1') as H12 by (apply ksqr_div_6_k_div_6; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 6 * (6 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 6 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 6 z2') as H17 by (apply ksqr_div_6_k_div_6; auto). specialize (H5 6). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma kcub_even_k_even : forall k,
  Z.Even (k^3) -> Z.Even k.
Proof.
  intros k H1. pose proof lemma_2_8' k as [H2 | H2].
  - auto.
  - destruct H2 as [k' H2]. assert (Z.Odd (k^3)) as H3.
    { exists (4*k'^3 + 6*k'^2 + 3*k'). nia. } rewrite <- Zodd_equiv in H3.
    rewrite <- Zeven_equiv in H1. apply Zodd_not_Zeven in H3. tauto.
Qed.

Lemma lemma_2_13_b : irrational (Rpower 2 (1/3)).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (H2 : Rpower 2 (1/3) <> 0%R). 
  { assert (H3 : (Rpower 2 0 < Rpower 2 (1/3))%R) by (apply Rpower_lt; lra). rewrite Rpower_O in H3; lra. }
  assert (z1 <> 0 /\ z2 <> 0) as [H3 H4].
  { assert (z1 = 0 \/ z2 = 0 \/ z1 <> 0 /\ z2 <> 0) as [H3 | [H3 | H3]] by lia; auto; rewrite H3 in H1; try rewrite Rdiv_0_l in H1; try rewrite Rdiv_0_r in H1; lra. }
  assert (H5 : exists z1' z2', ((Rpower 2 (1/3) = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H3. apply H4. apply H1. }
  destruct H5 as [z1' [z2' [H5 H6]]]. assert (H7 : (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3) = (IZR z1' / IZR z2') * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  assert (H8 : z1' <> 0 /\ z2' <> 0).
  { assert (z1' = 0 \/ z2' = 0 \/ z1' <> 0 /\ z2' <> 0) as [H8 | [H8 | H8]] by lia; auto; rewrite H8 in H5; try rewrite Rdiv_0_l in H5; try rewrite Rdiv_0_r in H5; lra. }
  replace (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3))%R with 2%R in H7.
  2 : { repeat rewrite <- Rpower_plus. replace (1/3 + 1/3 + 1/3)%R with 1%R by lra. rewrite Rpower_1;lra. }
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R with ((IZR z1')^3 / (IZR z2')^3)%R in H7 by (field; apply not_0_IZR; tauto).
    apply Rmult_eq_compat_r with (r := ((IZR z2')^3)%R) in H7. replace ((IZR z1' ^ 3 / IZR z2' ^ 3 * IZR z2' ^ 3)%R) with ((IZR z1')^3)%R in H7 by (field; apply not_0_IZR; tauto).
  replace 3 % nat with (Z.to_nat 3) in H7 at 1 by auto.
  assert (Z.Even (z1'^3)) as H9. 
  { replace 3 with (Z.of_nat 3) by auto. exists (z2'^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    apply eq_sym. rewrite pow_IZR in H7. replace (Z.of_nat (Z.to_nat 3)) with (3) in H7 by lia. apply H7. }
  assert (H10 : Z.Even z1'). { apply kcub_even_k_even in H9. auto. }
  assert (H11 : (2 | z1')). { destruct H10 as [k H10]. exists (k). lia. }
  destruct H10 as [k H10]. rewrite H10 in H7. assert (H12 : (IZR z2' ^ 3 = 4 * IZR (k^3))%R).
  { replace 3%nat with (Z.to_nat 3) in H7 by auto. rewrite pow_IZR with (z := 2 * k) in H7. replace (Z.to_nat 3) with 3%nat in H7 by auto.
    replace (Z.of_nat 3) with 3 in H7 by auto. replace ((2 * k) ^ 3) with (8 * k^3) in H7 by lia. rewrite mult_IZR in H7. nra. }
  assert (Z.Even (z2'^3)) as H13. 
  { replace 3 with (Z.of_nat 3) by auto. exists (2 * k^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    rewrite mult_IZR. replace (2 * (2 * IZR (k^3)))%R with (4 * IZR (k^3))%R by lra. nra. }
  assert (H14 : Z.Even z2'). { apply kcub_even_k_even in H13. auto. }
  assert (H15 : (2 | z2')). { destruct H14 as [k' H14]. exists (k'). lia. }
  specialize (H6 2) as [H6 | H6]; try lia; tauto.
Qed.

Lemma kcub_div_3_k_div_3 : forall k,
  Z.divide 3 (k^3) -> Z.divide 3 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 3*p \/ k = 3*p+1 \/ k = 3*p+2) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_b' : irrational (Rpower 3 (1/3)).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (H2 : Rpower 3 (1/3) <> 0%R). 
  { assert (H3 : (Rpower 3 0 < Rpower 3 (1/3))%R) by (apply Rpower_lt; lra). rewrite Rpower_O in H3; lra. }
  assert (z1 <> 0 /\ z2 <> 0) as [H3 H4].
  { assert (z1 = 0 \/ z2 = 0 \/ z1 <> 0 /\ z2 <> 0) as [H3 | [H3 | H3]] by lia; auto; rewrite H3 in H1; try rewrite Rdiv_0_l in H1; try rewrite Rdiv_0_r in H1; lra. }
  assert (H5 : exists z1' z2', ((Rpower 3 (1/3) = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H3. apply H4. apply H1. }
  destruct H5 as [z1' [z2' [H5 H6]]]. assert (H7 : (Rpower 3 (1/3) * Rpower 3 (1/3) * Rpower 3 (1/3) = (IZR z1' / IZR z2') * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  assert (H8 : z1' <> 0 /\ z2' <> 0).
  { assert (z1' = 0 \/ z2' = 0 \/ z1' <> 0 /\ z2' <> 0) as [H8 | [H8 | H8]] by lia; auto; rewrite H8 in H5; try rewrite Rdiv_0_l in H5; try rewrite Rdiv_0_r in H5; lra. }
  replace (Rpower 3 (1/ 3) * Rpower 3 (1/3) * Rpower 3 (1/3))%R with 3%R in H7. 
  2 : { repeat rewrite <- Rpower_plus. replace (1/3 + 1/3 + 1/3)%R with 1%R by lra. rewrite Rpower_1;lra. }
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R with ((IZR z1')^3 / (IZR z2')^3)%R in H7 by (field; apply not_0_IZR; tauto).
    apply Rmult_eq_compat_r with (r := ((IZR z2')^3)%R) in H7. replace ((IZR z1' ^ 3 / IZR z2' ^ 3 * IZR z2' ^ 3)%R) with ((IZR z1')^3)%R in H7 by (field; apply not_0_IZR; tauto).
  replace 3 % nat with (Z.to_nat 3) in H7 at 1 by auto. assert (3 | z1'^3) as H9.
  { replace 3 with (Z.of_nat 3) by auto. exists (z2'^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR.
    apply eq_sym. rewrite pow_IZR in H7. simpl in *. nra. }
  assert (H10 : Z.divide 3 z1'). { apply kcub_div_3_k_div_3 in H9. auto. }
  destruct H10 as [k H10]. rewrite H10 in H7. assert (H11 : (IZR z2' ^ 3 = 9 * IZR (k^3))%R).
  { replace 3%nat with (Z.to_nat 3) in H7 by auto. rewrite pow_IZR with (z := k * 3) in H7. replace (Z.to_nat 3) with 3%nat in H7 by auto.
    replace (Z.of_nat 3) with 3 in H7 by auto. replace ((k * 3) ^ 3) with (27 * k^3) in H7 by lia. rewrite mult_IZR in H7. nra. }
  assert (Z.divide 3 (z2'^3)) as H12. { replace 3 with (Z.of_nat 3) by auto. exists (3 * k^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    rewrite mult_IZR. replace (IZR (Z.of_nat 3)) with 3%R by auto. nra. }
  assert (H13 : Z.divide 3 z2'). { apply kcub_div_3_k_div_3 in H12. auto. }
  assert (H14 : (3 | z1')). { exists (k). lia. }
  specialize (H6 3) as [H6 | H6]; try lia; tauto.
Qed.

Lemma rational_plus_rev : forall a b,
  rational (a + b) -> rational a -> rational b.
Proof.
  intros a b H1 H2. unfold rational in *. destruct H1 as [z1 [z2 H1]]. destruct H2 as [z3 [z4 H2]].
  assert (a = 0 /\ b = 0 \/ a = 0 /\ b <> 0 \/ a <> 0 /\ b = 0 \/ a <> 0 /\ b <> 0)%R as [H3 | [H3 | [H3 | H3]]] by lra.
  - exists 0, 0. lra.
  - exists z1, z2. lra.
  - exists 0, 0. lra.
  - assert (a + b = 0 \/ a + b <> 0)%R as [H4 | H4] by lra.
    -- exists (-z3), z4. replace (-z3) with (-1 * z3) by lia. rewrite mult_IZR. lra.
    -- exists (z1 * z4 - z2 * z3), (z2 * z4).  rewrite minus_IZR. repeat rewrite mult_IZR. pose proof H1 as H1'. rewrite H2 in H1.
       apply Rminus_eq_compat_r with (r := (IZR z3 / IZR z4)%R) in H1. replace ((IZR z3 / IZR z4 + b - IZR z3 / IZR z4)%R) with b in H1 by lra.
       rewrite H1.  destruct H3 as [H3 H3']. 
       field; split; apply not_0_IZR; try apply x_neq_0_IZR_den_neq_0 with (x := (a + b)%R) (y := z1) (z := z2); try apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z3) (z := z4); auto.
Qed.

Lemma rational_mult_rev : forall a b,
  (a <> 0)%R -> rational (a * b) -> rational a -> rational b.
Proof.
  intros a b H1 H2 H3. unfold rational in *. destruct H2 as [z1 [z2 H2]]. destruct H3 as [z3 [z4 H3]].
  assert (a = 0 /\ b = 0 \/ a = 0 /\ b <> 0 \/ a <> 0 /\ b = 0 \/ a <> 0 /\ b <> 0)%R as [H4 | [H4 | [H4 | H4]]] by lra.
  - lra.
  - lra.
  - exists 0, 0. lra.
  - assert (a * b = 0 \/ a * b <> 0)%R as [H5 | H5] by lra.
    -- nra.
    -- exists (z1 * z4), (z2 * z3). repeat rewrite mult_IZR. pose proof H2 as H2'. rewrite H3 in H2.
       assert (H6 : IZR z1 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_num_neq_0 with (x := (a * b)%R) (y := z1) (z := z2); split; auto. }
       assert (H7 : IZR z3 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z3) (z := z4); split; auto. }
       assert (H8 : IZR z2 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_den_neq_0 with (x := (a * b)%R) (y := z1) (z := z2); split; auto. }
       assert (H9 : IZR z4 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z3) (z := z4); split; auto. }
       apply Rmult_eq_compat_r with (r := (IZR z4 / IZR z3)%R) in H2. replace ((IZR z3 / IZR z4 * b * (IZR z4 / IZR z3))%R) with b in H2 by (field; lra).
       rewrite H2. field; auto.
Qed.

Lemma lemma_2_14_a : irrational (sqrt 2 + sqrt 6).
Proof.
  assert (irrational (sqrt 2 + sqrt 6) \/ rational (sqrt 2 + sqrt 6)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 6 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 6 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 6)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 6)^2)%R with (8 + 4 * sqrt 3)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (sqrt (6 * 2)) with (2 * sqrt 3)%R. 2 : { replace (6 * 2)%R with ((2 * 2) * 3)%R by lra. 
      rewrite sqrt_mult_alt; try lra. rewrite sqrt_square; lra. } lra.
    }
    apply rational_plus_rev with (a := 8%R) (b := (4 * sqrt 3)%R) in H3 as H4.
    2 : { exists 8, 1. lra. }
    apply rational_mult_rev with (a := 4%R) (b := sqrt 3) in H4 as H5.
    2 : { lra. }
    2 : { exists 4, 1. lra. }
    pose proof lemma_2_13_a as H6. unfold irrational in H6. tauto.
Qed.

Lemma lemma_2_14_b : irrational (sqrt 2 + sqrt 3).
Proof.
  assert (irrational (sqrt 2 + sqrt 3) \/ rational (sqrt 2 + sqrt 3)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 3 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 3 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 3)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 3)^2)%R with (5 + 2 * sqrt 6)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (2 * 3)%R with 6%R by lra. replace (3 * 2)%R with 6%R by lra. nra.
    }
    apply rational_plus_rev with (a := 5%R) (b := (2 * sqrt 6)%R) in H3 as H4.
    2 : { exists 5, 1. lra. }
    apply rational_mult_rev with (a := 2%R) (b := sqrt 6) in H4 as H5.
    2 : { lra. }
    2 : { exists 2, 1. lra. }
    pose proof lemma_2_13_a'' as H6. unfold irrational in H6. tauto.
Qed.

Close Scope Z_scope.

Open Scope R_scope.

Lemma lemma_2_15_a : forall x p q m,
  rational p -> rational q -> x = p + sqrt q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ x^m = a + b * sqrt q.
Proof.
  intros x p q m H1 H2 H3 H4. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H5 [H6 H7]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    -- simpl. rewrite H7. rewrite H3. replace ((p + sqrt q) * (a + b * sqrt q)) with (p * a + p * b * sqrt q + sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra. 
Qed.

Lemma lemma_2_15_b : forall p q m,
  rational p -> rational q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ (p - sqrt q)^m = a - b * sqrt q.
Proof.
  intros p q m H1 H2 H3. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H4 [H5 H6]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    --  simpl. rewrite H6. replace ((p - sqrt q) * (a - b * sqrt q)) with (p * a - p * b * sqrt q - sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra.
Qed.

Lemma  lemma_2_16_a : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 < 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) > 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 < 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_lt_compat_r with (r := (INR n)^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. }
    apply Rmult_gt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2 : { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_lt_reg_r with (r := INR(m + n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_lt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 > 0). {
      apply Rmult_lt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_lt_reg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rgt_lt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_pos; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma Rmult_gt_reg_neg_r : forall r r1 r2,
  r < 0 -> r1 * r > r2 * r -> r1 < r2.
Proof.
  intros. nra.
Qed.

Lemma lemma_2_16_b : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 > 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) < 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 > 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_gt_compat_r with (r := (INR n)^2) in H3. 2: { nra. } field_simplify in H3. 2: { nra. }
    apply Rmult_lt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2: { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_gt_reg_r with (r := INR (m+n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_gt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 < 0). {
      apply Rmult_gt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_gt_reg_neg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rlt_gt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_neg; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma cross_multiply_lt : forall r1 r2 r3 r4,
  r1 > 0 -> r2 > 0 -> r3 > 0 -> r4 > 0 ->
  r1 * r4 < r2 * r3 -> r1 / r2 < r3 / r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 H3 H4 H5. apply Rmult_lt_reg_r with (r := r2); 
  apply Rmult_lt_reg_r with (r := r4); field_simplify; nra.
Qed.

Lemma gte_1_INR : forall n,
  (n > 0)%nat -> INR n >= 1.
Proof.
  intros n H1. assert ((n = 1 \/ n > 1)%nat) as [H2 | H2]. { lia. }
  - rewrite H2. simpl. lra.
  - apply Rgt_ge. apply lt_1_INR. lia.
Qed.

Lemma lemma_2_16_c : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> INR m / INR n < sqrt 2 ->
    exists m' n', INR m / INR n < INR m' / INR n' < sqrt 2.
Proof.
  intros m n H1 H2 H3. assert (INR n >= 1 /\ INR m >= 1) as [H4 H5] by (split; apply gte_1_INR; auto).
  set (m1 := (m + 2 * n)%nat). set (n1 := (m + n)%nat).
  assert (INR m1 >= 1 /\ INR n1 >= 1) as [H6 H7]. { split. unfold m1. apply gte_1_INR. lia. unfold n1. apply gte_1_INR. lia. }
  assert ((m1 >= 1 /\ n1 >= 1)%nat) as [H8 H9] by (split; lia).
  assert (H10: (INR m^2 / INR n^2) < 2). { apply Rsqr_incrst_1 in H3. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. } 2 : { apply sqrt_pos. }
  unfold Rsqr in H3. field_simplify in H3. 2 : { nra. } replace (sqrt 2 ^2) with 2 in H3. 2 : { simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt; nra. } nra. }
  pose proof lemma_2_16_a m n H1 H2 H10 as [H11 H12]. pose proof H11 as H13. replace ((m + 2 * n)%nat) with (m1) in H13; auto. replace ((m + n)%nat) with (n1) in H13; auto.
  pose proof lemma_2_16_b m1 n1 H9 H8 H13 as [H14 H15]. 
  exists ((m1 + 2 * n1)%nat), ((m1 + n1)%nat). split.
  2 : { apply sqrt_lt_1 in H14; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. rewrite Rmult_1_r. repeat rewrite plus_INR. nra.
  simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. } replace ((INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2)) with ((INR (m1 + 2 * n1) / INR (m1 + n1))^2) in H14.
  2 : { field. rewrite plus_INR. nra. } rewrite sqrt_pow2 in H14. nra. apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. repeat rewrite plus_INR. nra.
  repeat rewrite plus_INR. nra. }
  assert (H16 : 0 <= INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2).
  { split; auto; apply Rlt_le. apply Rdiv_pos_pos. rewrite plus_INR. rewrite mult_INR. simpl. nra. rewrite plus_INR. nra. }
  assert (H17 : INR (m1 + 2 * n1) / INR (m1 + n1) < sqrt 2). 
  { pose proof sqrt_lt_1_alt (INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) 2 H16 as H17. rewrite sqrt_div in H17.
    - rewrite sqrt_pow2 in H17. rewrite sqrt_pow2 in H17. auto. rewrite plus_INR. nra. rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. nra. }
  assert (H18 : 2 - INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 > INR m ^ 2 / INR n ^ 2 - 2) by nra.
  assert (H19 : INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 - 2 > INR m ^ 2 / INR n ^ 2 - 2).
  { replace (INR m1 ^2) with (INR (m + 2 * n)^2) in H15. 2 : { unfold m1. auto. } 
    replace (INR n1^2) with (INR (m + n)^2) in H15. 2 : { unfold n1. auto. } nra. }
  assert (H20 : 2 - INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2 - INR m ^ 2 / INR n ^ 2) by nra.
  assert (H21 : INR m ^ 2 / INR n ^ 2 < INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) by nra.
  apply sqrt_lt_1 in H21; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
  rewrite sqrt_div in H21; try nra. rewrite sqrt_div in H21; try nra. 2 : { rewrite plus_INR. nra. }
  rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. rewrite mult_INR. simpl. nra. } rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. nra. } nra.
Qed.

Open Scope Z_scope.  

Fixpoint max_list_Z (l : list Z) : Z :=
  match (l) with
  | [] => 0
  | x :: xs => Z.max x (max_list_Z xs)
  end.

Lemma in_list_le_max : forall l x,
  In x l -> x <= (max_list_Z l)%Z.
Proof.
  intros l x H. induction l as [| h t IH].
  - inversion H.
  - destruct H as [H | H].
    -- rewrite H. simpl. apply Z.le_max_l.
    -- apply IH in H. simpl. lia.
Qed.

Definition prime_list (l : list Z) : Prop := Forall Znt.prime' l.

Lemma prime_list_fold_right_pos : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2. assert (h >= 2) as H3.
    { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma in_prime_list : forall l x,
  prime_list l -> In x l -> Znt.prime' x.
Proof.
  intros l x H1 H2. unfold prime_list in H1. rewrite Forall_forall in H1. apply H1. auto.
Qed.

Definition first_n_primes (l : list Z) : Prop :=
  NoDup l /\ prime_list l /\
    (forall x, (Znt.prime' x /\ x <= (max_list_Z l)%Z) -> In x l).

Lemma div_trans : forall a b c,
  (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [k1 H1] [k2 H2]. unfold Z.divide. exists (k1 * k2). lia.
Qed.

Lemma prime_divides : forall z,
  z > 1 -> (exists p, Znt.prime' p /\ (p | z)).
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1] by lia.
  - lia.
  - apply strong_induction_Z with (n := z). 2 : { lia. }
    intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
    + exists 2. split.
      * rewrite Znt.prime_alt. apply Znt.prime_2.
      * exists (1). lia.
    + destruct (Znt.prime_dec n) as [H4 | H4].
      * exists n. split.
        -- rewrite Znt.prime_alt. auto.
        -- exists (1). lia.
      * rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4. destruct H4 as [H4 | H4].
        -- lia.
        -- apply not_all_ex_not in H4. destruct H4 as [p H4]. apply imply_to_and in H4. destruct H4 as [H4 H5].
           assert (p <= n) as H6 by lia. assert (p > 1) as H7 by lia. apply NNPP in H5. assert (0 <= p < n) as H9 by lia.
           specialize (IH p H9 H7). destruct IH as [p' IH]. exists p'. split.
            ++ apply IH.
            ++ apply div_trans with (b := p); (try apply IH; try apply H5).
Qed.

Lemma prime_no_div : forall p z,
  Znt.prime' p -> (p | z) -> ~(p | z + 1).
Proof.
  intros p z H1 H2 H3. destruct H2 as [r H2]. destruct H3 as [s H3].
  assert (p | 1) as H4 by (exists (s - r); lia). assert (p >= 2) as H5.
  { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
  assert (p = 1) as H6. { destruct H4 as [t H4]. assert (t > 0) by lia. nia. }
  lia.
Qed.

Lemma fold_right_mul_distributive : forall (k : Z) (l : list Z),
  fold_right Z.mul k l = k * fold_right Z.mul 1 l.
Proof.
  intros k l. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma fold_right_factor_divides : forall (k : Z) (l : list Z),
  (In k l) -> (k | fold_right Z.mul 1 l).
Proof.
  intros k l H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma prime_list_product_gt_1 : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 1.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. unfold prime_list in *. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2.
    assert (h >= 2) as H3. { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma lemma_2_17_a : forall z : Z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1] by lia.
  - lia.
  - apply strong_induction_Z with (n := z). 2 : { lia. }
    intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
    + exists [2]. split.
      * constructor. rewrite Znt.prime_alt. apply Znt.prime_2. constructor.
      * simpl. lia.
    + destruct (Znt.prime_dec n) as [H4 | H4].
      * exists [n]. split.
        -- constructor. rewrite Znt.prime_alt. auto. constructor.
        -- simpl. lia.
      * rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4. destruct H4 as [H4 | H4].
        -- lia.
        -- apply not_all_ex_not in H4. destruct H4 as [p H4]. apply imply_to_and in H4. destruct H4 as [H4 H5].
           apply NNPP in H5. destruct H5 as [k H5]. assert (p > 1 /\ 0 <= p < n) as [H7 H8] by lia.
           assert (k > 1 /\ 0 <= k < n) as [H9 H10] by nia.
           assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
           assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; lia).
           exists (l1 ++ l2). split.
           ++ apply Forall_app. split.
              ** apply H11.
              ** apply H12.
           ++ destruct H11 as [H11 H11']. destruct H12 as [H12 H12']. rewrite fold_right_app. rewrite <- H12'.
              rewrite fold_right_mul_distributive. rewrite <- H11'. lia.
Qed.

Lemma prime_list_product_exists_pos : forall z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (lemma_2_17_a z) as H2. apply H2 in H1. destruct H1 as [l [H1 H3]]; exists l; split; auto; try lia.
Qed.

Lemma prime_list_product_exists_neg : forall z,
  z < -1 -> exists l : list Z,
    prime_list l /\ z = -fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (lemma_2_17_a (-z)) as H2. assert (-z > 1) as H3 by lia.
  apply H2 in H3. destruct H3 as [l [H3 H4]]; exists l; split; auto; try lia.
Qed.

Lemma prime_list_cons : forall l p,
  prime_list (p :: l) -> prime_list l /\ Znt.prime' p.
Proof.
  intros l p H1. split.
  - apply Forall_inv_tail in H1. apply H1.
  - apply Forall_inv in H1. apply H1.
Qed.

Lemma prime_list_cons_iff : forall l p,
  prime_list (p :: l) <-> prime_list l /\ Znt.prime' p.
Proof.
  intros l p. split.
  - apply prime_list_cons.
  - intros [H1 H2]. apply Forall_cons; auto.
Qed.

Lemma prime_list_app : forall l1 l2,
  prime_list (l1 ++ l2) <-> prime_list l1 /\ prime_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold prime_list in H1. rewrite Forall_app in H1. tauto.
  - intros [H1 H2]. unfold prime_list. rewrite Forall_app. tauto.
Qed.

Lemma in_div_fold_right : forall l z,
  In z l -> (z | fold_right Z.mul 1 l).
Proof.
  intros l z H. induction l as [| h t IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma divide_factor_l : forall a b c,
  (b | c) -> (a * b | a * c).
Proof.
  intros a b c [k H]. exists k. lia.
Qed.

Lemma count_mul_div_fold_right : forall l z,
  In z l -> (z ^ (Z.of_nat (count_occ Z.eq_dec l z)) | fold_right Z.mul 1 l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    -- rewrite H1. destruct (Z.eq_dec z z) as [H2 | H2]; try contradiction. clear H2.
       assert (In z t \/ ~ In z t) as [H2 | H2] by apply classic.
       + replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + apply (count_occ_not_In Z.eq_dec) in H2. rewrite H2. simpl. exists (fold_right Z.mul 1 t). lia. 
    -- pose proof (Z.eq_dec h z) as [H2 | H2].
       + rewrite H2. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. clear H3.
         replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + destruct (Z.eq_dec h z) as [H3 | H3]; try contradiction. apply IH in H1. destruct H1 as [r H1]. exists (r * h). lia.
Qed.

Lemma p_div_fold_right_In : forall l p,
  prime_list l -> Znt.prime' p -> (p | fold_right Z.mul 1 l) -> In p l.
Proof.
  intros l p H1 H2 H3. induction l as [| h t IH].
  - simpl in H3. rewrite Znt.prime_alt in H2. apply Znt.prime_ge_2 in H2. destruct H3 as [r1 H3]. assert (r1 = 1) as H4 by lia. lia.
  - simpl in H3. apply prime_list_cons in H1 as [H1 H1']. destruct (Z.eq_dec h p) as [H6 | H6].
    + rewrite H6. left. reflexivity.
    + right. apply IH. rewrite Znt.prime_alt in H2. auto. apply Znt.prime_mult in H3. 2 : { rewrite Znt.prime_alt in H2. auto. }
      assert (H7 : ~(p | h)). { intros H7. apply Znt.prime_div_prime in H7; try lia; rewrite Znt.prime_alt in H1', H2; auto. }
      tauto.
Qed.

Lemma p_notin_ndiv_fold_right : forall l p,
  prime_list l -> Znt.prime' p -> ~In p l -> ~(p | fold_right Z.mul 1 l).
Proof.
  intros l p H1 H2 H3 H4. apply p_div_fold_right_In in H4; auto.
Qed.

Lemma div_a_mul_p_pow : forall a b c d,
  (c > 0)%nat -> a = b * d^(Z.of_nat c) -> (d | a).
Proof.
  intros a b c p H1 H2. destruct c; try lia. rewrite Nat2Z.inj_succ in H2. rewrite Z.pow_succ_r in H2; try lia.
  exists (b * p ^ Z.of_nat c). lia.
Qed.

Lemma div_mul_factor : forall a b c d,
  b <> 0 -> a * b = c * d -> (b | d) -> a = c * (d / b).
Proof.
  intros a b c d H1 H2 [k H3]. rewrite H3. rewrite Z.div_mul; auto. rewrite H3 in H2. apply Z.mul_cancel_l with (p := b); auto. lia.
Qed.

Lemma z_pow_zero : forall a : Z,
  a <> 0 -> 0^a = 0.
Proof.
  intros a H1. assert (a < 0 \/ a = 0 \/ a = 1 \/ a > 1) as [H2 | [H2 | [H2 | H2]]] by lia.
  - rewrite Z.pow_neg_r; lia.
  - rewrite H2. lia.
  - rewrite H2. lia.
  - replace a with (Z.succ (a - 1)) by lia. rewrite Z.pow_succ_r; lia.
Qed.

Lemma fold_right_div_pow_eq_remove_fold_right : forall l z,
  z <> 0 ->
  fold_right Z.mul 1 l / (z ^ (Z.of_nat (count_occ Z.eq_dec l z))) = fold_right Z.mul 1 (remove Z.eq_dec z l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - simpl. apply Z.div_1_r.
  - assert (In z (h :: t) \/ ~ In z (h :: t)) as [H2 | H2] by apply classic.
    -- simpl. destruct (Z.eq_dec h z) as [H3 | H3].
       + rewrite H3. destruct (Z.eq_dec z z) as [H4 | H4]; try contradiction. clear H4.
         assert (In z t \/ ~ In z t) as [H4 | H4] by apply classic.
         * rewrite <- IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } pose proof (count_mul_div_fold_right t z H4) as [r H5].
           rewrite H5. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H4. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
              replace (z^Z.of_nat (count_occ Z.eq_dec t z) * z) with (z * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.div_mul; try lia.
              assert (H6 : z ^ Z.of_nat (count_occ Z.eq_dec t z) <> 0). { apply Z.pow_nonzero; lia. } lia.
         * replace (count_occ Z.eq_dec t z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H4. lia. }
           replace (remove Z.eq_dec z t) with t. 2 : { apply (notin_remove Z.eq_dec) in H4. auto. } rewrite Z.mul_comm. replace (Z.of_nat 1) with 1 by lia.
           rewrite Z.pow_1_r. rewrite Z.div_mul; try lia.
       + destruct (Z.eq_dec z h) as [H4 | H4]; try lia. clear H4. simpl. rewrite <- IH. destruct H2 as [H2 | H2]; try contradiction. pose proof (count_mul_div_fold_right t z H2) as [r H4].
         rewrite H4. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
         replace (z^Z.of_nat (count_occ Z.eq_dec t z) * h) with (h * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
         apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero; lia.
    -- replace (remove Z.eq_dec z (h :: t)) with (h :: t). 2 : { apply (notin_remove Z.eq_dec) in H2. auto. } 
       replace (count_occ Z.eq_dec (h :: t) z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H2. lia. } simpl. rewrite Z.div_1_r. lia.
Qed.

Lemma p_ndiv_fold_right : forall l p,
  prime_list l -> In p l -> ~(p | (fold_right Z.mul 1 l / p ^ (Z.of_nat (count_occ Z.eq_dec l p)))).
Proof.
  intros l p H1 H2. rewrite fold_right_div_pow_eq_remove_fold_right. 
  2 : { apply in_prime_list in H2; auto. rewrite Znt.prime_alt in H2. apply Znt.prime_ge_2 in H2. lia. }
  intros H3. assert (~In p (remove Z.eq_dec p l)) as H4. { intros H4. apply (in_remove Z.eq_dec) in H4. lia. }
  apply H4. apply p_div_fold_right_In; auto. 2 : { apply in_prime_list in H2; auto. } unfold prime_list in *.
  rewrite Forall_forall in *. intros x H5. apply H1. apply in_remove in H5. tauto.
Qed.

Lemma z_pow_div_z_div : forall a b c,
  c >= 1 -> (a^c | b) -> (a | b).
Proof.
  intros a b c H1 [k H2]. exists (k * a^(Z.pred c)). rewrite H2.
  - assert (c = 1 \/ c > 1) as [H3 | H3] by lia.
    + rewrite H3. simpl. lia.
    + assert (H4 : exists d, c = Z.succ d) by (exists (Z.pred c); lia). destruct H4 as [d H4]. rewrite H4. rewrite Z.pow_succ_r. 2 : { lia. }
      replace (Z.pred (Z.succ d)) with d by lia. lia.
Qed.

Lemma z_mul_div : forall a b c,
  c <> 0 ->
  (c | b) -> a * (b / c) = (a * b) / c.
Proof.
  intros a b c H1 [r1 H2]. rewrite H2. rewrite Z.div_mul; auto. 
  rewrite Z.mul_assoc. rewrite Z.div_mul; auto.
Qed.

Lemma z_pow_mult : forall a b c,
  a >= 0 -> b >= 0 -> c >= 0 -> a^(b) * a^(c) = a^(b + c).
Proof.
  intros a b c H1 H2 H3. rewrite Z.pow_add_r; lia.
Qed.

Lemma prime_factorization_unique : forall l1 l2 z p,
  prime_list l1 -> prime_list l2 -> z = fold_right Z.mul 1 l1 -> z = fold_right Z.mul 1 l2 -> 
  count_occ Z.eq_dec l1 p = count_occ Z.eq_dec l2 p.
Proof.
  intros l1 l2 z p H1 H2 H3 H4.
  pose proof (lt_eq_lt_dec (count_occ Z.eq_dec l1 p) (count_occ Z.eq_dec l2 p)) as [[H5 | H5] | H5].
  2 : { auto. }
  - assert (H6 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H6) as H7.
    rewrite <- H4 in H7. assert (count_occ Z.eq_dec l1 p = 0 \/ count_occ Z.eq_dec l1 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l1). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l1)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H3 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l2 p)); auto; lia. } tauto.
    -- assert (H9 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H9) as H10.
       rewrite <- H3 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l1 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1)). rewrite H10. rewrite Z.div_mul. 
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l1 p) | p ^ Z.of_nat (count_occ Z.eq_dec l2 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p) + Z.of_nat (count_occ Z.eq_dec l1 p)) with (Z.of_nat (count_occ Z.eq_dec l2 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l1 p H1 H9 as H12. rewrite <- H3 in H12. tauto.
  - assert (H6 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H6) as H7.
    rewrite <- H3 in H7. assert (count_occ Z.eq_dec l2 p = 0 \/ count_occ Z.eq_dec l2 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l2). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l2)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H4 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l1 p)); auto; lia. }
       tauto.
    -- assert (H9 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H9) as H10.
       rewrite <- H4 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l2 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1)). rewrite H10. rewrite Z.div_mul.
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l2 p) | p ^ Z.of_nat (count_occ Z.eq_dec l1 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p) + Z.of_nat (count_occ Z.eq_dec l2 p)) with (Z.of_nat (count_occ Z.eq_dec l1 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l2 p H2 H9 as H12. rewrite <- H4 in H12. tauto.
Qed.

Lemma fold_right_mult_app_Z : forall l1 l2,
  fold_right Z.mul 1 (l1 ++ l2) = fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h1 t1 IH].
  - replace (fold_right Z.mul 1 []) with 1 by reflexivity. replace ([] ++ l2) with l2 by reflexivity. lia.
  - simpl. rewrite IH. lia.
Qed.

Fixpoint repeat_app (l : list Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => l ++ repeat_app l n'
  end. 

Lemma in_repeat_app : forall l n z,
  In z (repeat_app l n) -> In z l.
Proof.
  intros l n z H. induction n as [| n' IH].
  - simpl in H. contradiction.
  - simpl in H. apply in_app_or in H. destruct H as [H | H]; auto.
Qed.

Lemma count_occ_repeat_app : forall l n z,
  count_occ Z.eq_dec (repeat_app l n) z = (n * count_occ Z.eq_dec l z)%nat.
Proof.
  intros l n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. rewrite count_occ_app. rewrite IH. lia.
Qed.

Lemma count_occ_repeat_eq : forall n z,
  count_occ Z.eq_dec (repeat z n) z = n.
Proof.
  intros n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. destruct (Z.eq_dec z z) as [H1 | H1].
    + rewrite IH. lia.
    + contradiction.
Qed.

Lemma count_occ_repeat_possible_equal : forall h n z,
  count_occ Z.eq_dec (repeat h n) z = (if Z.eq_dec h z then n else 0)%nat.
Proof.
  intros h n z. induction n as [| n' IH].
  - simpl. destruct (Z.eq_dec h z); lia.
  - simpl. destruct (Z.eq_dec h z) as [H1 | H1].
    + rewrite H1 in *. lia.
    + apply IH.
Qed.

Lemma count_occ_2n_exist_app : forall l1 l2 n,
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
    exists l3, forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec (l3 ++ l3) z)%nat.
Proof.
  intros l1 l2 n H1. destruct l1 as [| h t].
  - exists l2. intros z. simpl in H1. rewrite Nat.mul_0_r in H1. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  - exists (repeat h n ++ repeat_app t n). intros z. specialize (H1 z). rewrite H1. repeat rewrite count_occ_app. 
    repeat rewrite count_occ_repeat_app. destruct (Z.eq_dec h z) as [H2 | H2].
    -- rewrite H2. repeat rewrite count_occ_repeat_eq. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. lia.
    -- repeat rewrite count_occ_repeat_possible_equal. destruct (Z.eq_dec z h) as [H3 | H3].
       + rewrite H3. simpl. destruct (Z.eq_dec h h) as [H4 | H4]; try contradiction. lia.
       + destruct (Z.eq_dec h z) as [H4 | H4]; try contradiction. simpl. 
         destruct (Z.eq_dec h z) as [H5 | H5]; try contradiction. lia.
Qed.

Lemma repeat_app_nil : forall (l : list Z) n,
  repeat_app [] n = [].
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma z_square_even_primes : forall z,
  (z > 1)%Z -> exists l, prime_list l /\ z^2 = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p)).
Proof.
  intros z H1. pose proof (lemma_2_17_a z H1) as [l [H2 H3]].
  exists (l ++ l). repeat split.
  - apply Forall_app; split; auto.
  - rewrite fold_right_mult_app_Z. lia.
  - intros p. rewrite count_occ_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Lemma fold_right_repeat_app : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ Z.of_nat n.
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity.
    rewrite fold_right_mult_app_Z. rewrite IH. rewrite <- Z.pow_succ_r; lia.
Qed.

Lemma z_pow_factor_primes : forall z k,
  (z > 1)%Z -> exists l, prime_list l /\ z^Z.of_nat k = fold_right Z.mul 1 l /\ (forall p, exists q, (count_occ Z.eq_dec l p) = q * k)%nat.
Proof.
  intros z k H1. pose proof (lemma_2_17_a z H1) as [l [H2 H3]].
  exists (repeat_app l k). repeat split.
  - apply Forall_forall. intros x H4. apply in_repeat_app in H4. apply in_prime_list in H4; auto.
  - rewrite fold_right_repeat_app. rewrite H3. lia.
  - intros p. rewrite count_occ_repeat_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Fixpoint remove_one {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                        (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if eq_dec x a then xs else x :: remove_one eq_dec a xs
  end.

Fixpoint reduce_freq_to_half {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                      (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => 
      let freq := count_occ eq_dec l x in
      repeat x (Nat.div2 freq) ++ remove eq_dec x (reduce_freq_to_half eq_dec xs)
  end.  

Fixpoint reduce_freq_by_factor {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                (k : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      let freq := count_occ eq_dec l x in
      repeat x (freq / k) ++ remove eq_dec x (reduce_freq_by_factor eq_dec k xs)
  end.

Lemma remove_one_In : forall {A : Type} eq_dec (a : A) l,
  In a l -> count_occ eq_dec (remove_one eq_dec a l) a = pred (count_occ eq_dec l a).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct (eq_dec h a) as [H3 | H3]; try contradiction. reflexivity.
Qed.

Lemma remove_one_not_In : forall {A : Type} eq_dec (a : A) l,
  ~In a l -> remove_one eq_dec a l = l.
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + rewrite H2 in H1. rewrite not_in_cons in H1. tauto.
    + simpl. rewrite IH; auto. rewrite not_in_cons in H1. tauto.
Qed.

Lemma count_occ_remove_one_not_eq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma Z_div_mult_good : forall a b, 
  (a <> 0) -> a * b / a = b.
Proof.
  intros a b H1. rewrite Z.mul_comm. rewrite Z.div_mul; auto.
Qed.

Lemma In_0_fold_right_eq_0 : forall l,
  In 0 l -> fold_right Z.mul 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + apply IH in H1. lia.
Qed.

Lemma contra_2 : forall P Q,
  (P -> Q) -> (~Q -> ~P).
Proof.
  tauto.
Qed.

Lemma not_in_0_fold_right_neq_0 : forall l,
  ~In 0 l -> fold_right Z.mul 1 l <> 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply not_in_cons in H1 as [H1 H1']. destruct (Z.eq_dec h 0) as [H2 | H2].
    + rewrite H2. lia.
    + apply IH in H1'. lia.
Qed.

Lemma fold_right_remove_one_In : forall a l,
  ~In 0 l -> In a l -> fold_right Z.mul 1 (remove_one Z.eq_dec a l) = fold_right Z.mul 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl. destruct (Z.eq_dec h a) as [H3 | H3].
    + rewrite H3. replace (a * fold_right Z.mul 1 t / a) with (fold_right Z.mul 1 t).
      2 : { rewrite <- Z.mul_comm. rewrite Z.div_mul; auto. apply not_in_cons in H1. lia. }
      lia.
    + simpl. destruct H2 as [H2 | H2]; try contradiction.
      rewrite IH; auto. 2 : { apply not_in_cons in H1. tauto. }
      apply in_div_fold_right in H2 as [r H2]. rewrite H2. rewrite Z.div_mul. 
      2 : { apply not_in_cons in H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia. }
      rewrite Z.mul_assoc. rewrite Z.div_mul; auto. apply not_in_cons in H1. 
      destruct H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia.
Qed.

Lemma fold_right_0_In : forall l,
  In 0 l -> fold_right Z.mul 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + apply IH in H1. lia.
Qed.

Lemma in_remove_in : forall a b l,
  In a (remove_one Z.eq_dec b l) -> In a l.
Proof.
  intros a b l H1. induction l as [| h t IH].
  - contradiction.
  - simpl in H1. destruct (Z.eq_dec h b) as [H2 | H2].
    + simpl. tauto.
    + simpl. destruct H1 as [H1 | H1].
      * left. auto.
      * tauto.
Qed.

Lemma remove_one_not_in_remove_one : forall (a b : Z) l,
  ~In a l -> ~In a (remove_one Z.eq_dec b l).
Proof.
  intros a b l H1 H2. apply H1. apply in_remove_in in H2. auto.
Qed.

Lemma count_occ_equ_fold_right : forall l1 l2,
  (forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec l1 z)%nat) ->
  fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 H1. assert (In 0 l2 \/ ~In 0 l2) as [H0 | H0] by apply classic.
  - specialize (H1 0). assert (In 0 l1). { apply (count_occ_In Z.eq_dec) in H0. apply (count_occ_In Z.eq_dec). lia. }
    repeat rewrite fold_right_0_In; auto.
  - assert (H0' : ~In 0 l1). { intros H2. apply H0. apply (count_occ_In Z.eq_dec) in H2. apply (count_occ_not_In Z.eq_dec) in H0. specialize (H1 0). lia. } 
    generalize dependent l2. induction l1 as [| h t IH].
    intros l2 H1. simpl in *. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  -- intros l2 H1 H2. simpl. simpl in H0'. apply not_or_and in H0' as [H0' H0'']. specialize (IH H0'' (remove_one Z.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Z.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
    }
    2 : { intros H3. apply (remove_one_not_in_remove_one 0 h l2) in H2. tauto. }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Z.eq_dec). lia. } rewrite fold_right_remove_one_In; auto. apply in_div_fold_right in H3 as [r H3]. rewrite H3. rewrite Z.div_mul; auto; lia.
Qed.

Lemma count_occ_double_n : forall z l1 l2 n,
  count_occ Z.eq_dec l2 z = (2 * n * count_occ Z.eq_dec l1 z)%nat -> count_occ Z.eq_dec (repeat_app l1 (2 * n)%nat) z = count_occ Z.eq_dec l2 z.
Proof.
  intros z l1 l2 n H1. rewrite count_occ_repeat_app. lia. 
Qed.

Lemma count_occ_double_n_prime : forall l1 l2 n,
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
  (forall z, (count_occ Z.eq_dec (repeat_app l1 (2 * n)) z = count_occ Z.eq_dec l2 z)%nat).
Proof.
  intros l1 l2 n H1 z. specialize (H1 z). rewrite count_occ_repeat_app. lia.
Qed.

Lemma fold_right_mult_repeat_app_Z : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ (Z.of_nat n).
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity. rewrite fold_right_mult_app_Z. rewrite IH.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } lia.  
Qed.

Lemma fold_right_double_n_count_square : forall l1 l2 (n : nat),
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
  (fold_right Z.mul 1 l1)^(Z.of_nat (2 * n)) = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 n H1. pose proof (count_occ_double_n_prime l1 l2 n H1) as H2. apply count_occ_equ_fold_right in H2. 
  rewrite H2. rewrite fold_right_mult_repeat_app_Z. reflexivity.
Qed.

Lemma even_count_occ_cons_eq : forall h t z,
  Nat.Even (count_occ Z.eq_dec (h :: t) z) -> z = h -> Nat.Odd (count_occ Z.eq_dec t z).
Proof.
  intros h t z H1 H2. induction t as [| h' t' IH].
  - rewrite H2 in H1. simpl in H1. destruct (Z.eq_dec h h) as [H3 | H3]; try lia. 
    assert (Nat.Odd 1) as H4. { unfold Nat.Odd. exists 0%nat. lia. } assert (~Nat.Even 1) as H5. { unfold Nat.Even. intros [k H5]. lia. }
    tauto.
  - rewrite H2. simpl. destruct (Z.eq_dec h' h) as [H3 | H3].
    + rewrite H3 in H1. rewrite H2 in H1. simpl in H1. destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
      apply Nat.Even_succ. apply H1.
    + rewrite H2 in *. apply IH. simpl in *. destruct (Z.eq_dec h h) as [H4 | H4]; try lia. rewrite Nat.Even_succ. apply IH.
      destruct (Z.eq_dec h' h) as [H5 | H5]; try contradiction. apply H1.
Qed.

Lemma even_count_odd_cons_neq : forall h t z,
  Nat.Even (count_occ Z.eq_dec (h :: t) z) -> z <> h -> Nat.Even (count_occ Z.eq_dec t z).
Proof.
  intros h t z H1 H2. induction t as [| h' t' IH].
  - simpl. exists 0%nat. lia.
  - simpl in *. repeat destruct (Z.eq_dec h' h) as [H3 | H3]; repeat destruct (Z.eq_dec h' z) as [H4 | H4]; 
    repeat destruct (Z.eq_dec h z) as [H5 | H5]; try lia; auto.
Qed.

Lemma count_occ_remove_neq : forall h t z,
  h <> z -> count_occ Z.eq_dec (remove Z.eq_dec h t) z = count_occ Z.eq_dec t z. 
Proof.
  intros h t z H1. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. repeat (simpl; destruct (Z.eq_dec h h') as [H2 | H2]); repeat (simpl; destruct (Z.eq_dec h' z) as [H3 | H3]); try lia.
Qed.

Lemma count_occ_0_count_occ_reduce_0 : forall l1 z,
  count_occ Z.eq_dec l1 z = 0%nat -> count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l1) z = 0%nat.
Proof.
  intros l1 z H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. destruct (Z.eq_dec h z) as [H2 | H2]; try lia. pose proof H1 as H1'. apply IH in H1. clear IH. simpl.
    destruct (Z.eq_dec h h) as [H3 | H3]; try lia. rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto.
    rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_0_count_occ_reduce_factor_0 : forall l1 z k,
  count_occ Z.eq_dec l1 z = 0%nat -> count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l1) z = 0%nat.
Proof.
  intros l1 z k H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. destruct (Z.eq_dec h z) as [H2 | H2]; try lia. pose proof H1 as H1'. apply IH in H1. clear IH. simpl.
    destruct (Z.eq_dec h h) as [H3 | H3]; try lia. rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto.
    rewrite count_occ_remove_neq; auto.
Qed.

Lemma remove_repeat : forall h n,
  remove Z.eq_dec h (repeat h n) = [].
Proof.
  intros h n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h) as [H1 | H1]; try lia. apply IH.
Qed.

Lemma count_occ_reduce_freq_not_in : forall l1 z,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l1) z = 0%nat.
Proof.
  intros l1 z H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_factor_not_in : forall l1 z k,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l1) z = 0%nat.
Proof.
  intros l1 z k H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma remove_repeat_neq : forall h h' n,
  h <> h' -> remove Z.eq_dec h (repeat h' n) = repeat h' n.
Proof.
  intros h h' n H1. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h') as [H2 | H2]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma count_occ_remove_eq : forall h t,
  count_occ Z.eq_dec (remove Z.eq_dec h t) h = 0%nat.
Proof.
  intros h t. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h') as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec h h) as [H2 | H2]; try lia. rewrite H1 in IH. apply IH.
    + simpl. destruct (Z.eq_dec h' h) as [H2 | H2]; try lia.
Qed.

Lemma count_occ_reduce_freq_to_half : forall l z,
  (Nat.div2 (count_occ Z.eq_dec l z) = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. reflexivity. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_by_factor : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_factor_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. apply Nat.Div0.div_0_l. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_to_half_prime : forall l z,
  (count_occ Z.eq_dec l z / 2 = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. pose proof (count_occ_reduce_freq_to_half l z) as H1. rewrite Nat.div2_div in H1. apply H1.
Qed.

Lemma count_occ_reduce_freq_by_factor_prime : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. pose proof (count_occ_reduce_freq_by_factor l z k) as H1. apply H1.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_to_half : forall l1 l2,
  (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> (l2 = reduce_freq_to_half Z.eq_dec l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (l2 ++ l2) z)%nat).
Proof.
  intros l1 l2 H1 H2 z. rewrite H2. rewrite count_occ_app. repeat rewrite <- count_occ_reduce_freq_to_half. 
  specialize (H1 z). destruct H1 as [n H1]. rewrite H1. rewrite div2_double. lia.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_by_factor : forall l1 l2 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> (l2 = reduce_freq_by_factor Z.eq_dec k l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (repeat_app l2 k) z)%nat).
Proof.
  intros l1 l2 k H1 H2 z. rewrite H2. rewrite count_occ_repeat_app. repeat rewrite <- count_occ_reduce_freq_by_factor. 
  specialize (H1 z). destruct H1 as [q H1]. rewrite H1. assert (k = 0 \/ k <> 0)%nat as [H3 | H3] by lia.
  - rewrite H3. simpl. lia.
  - rewrite Nat.div_mul; lia.
Qed.

Lemma fold_right_even_square : forall l1,
    (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> exists l2,
    fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^2.
Proof.
  intros l1 H1. set (l2 := reduce_freq_to_half Z.eq_dec l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_to_half l1 l2 H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_app_Z. nia. 
Qed.

Lemma fold_right_factor : forall l1 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> exists l2,
  fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^Z.of_nat k.
Proof.
  intros l1 k H1. set (l2 := reduce_freq_by_factor Z.eq_dec k l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_by_factor l1 l2 k H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_repeat_app_Z. reflexivity.
Qed.

Lemma even_count_occ_perfect_square : forall z,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p))) ->
    (exists m, z = m^2).
Proof.
  intros z [l [H1 H2]]. pose proof (fold_right_even_square l H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma count_occ_perfect_factor : forall z k,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, (exists q, (count_occ Z.eq_dec l p) = q * k)%nat)) ->
    (exists m, z = m^Z.of_nat k).
Proof.
  intros z k [l [H1 H2]]. pose proof (fold_right_factor l k H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma lemma_2_17_b : forall n : Z,
  (n >= 0)%Z ->
  (~(exists m, (n = m^2))%Z) -> irrational (sqrt (IZR n)).
Proof.
  intros n H1 H2 [a [b H3]]. unfold not in *. apply H2. assert (n = 0 \/ n > 0) as [H4 | H4] by lia.
  - exists 0. lia.
  - clear H1. rename H4 into H1.
    assert (Rsqr (sqrt (IZR n)) = Rsqr (IZR a / IZR b)) as H4 by (rewrite H3; reflexivity).
    rewrite Rsqr_def in H4. rewrite sqrt_def in H4. 2 : { apply IZR_le; lia. }
    assert (IZR n * IZR b ^ 2 = IZR a ^ 2)%R as H5.
    { 
      rewrite H4. repeat rewrite Rsqr_def. field. apply not_0_IZR. assert (b = 0 \/ b <> 0) as [H5 | H5] by lia; auto.
      rewrite H5 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_r in H4.
      apply eq_IZR_R0 in H4. lia. 
    }
    repeat rewrite pow_IZR in H5. rewrite <- mult_IZR in H5. apply eq_IZR in H5. replace (Z.of_nat 2) with 2%Z in H5 by reflexivity.
    assert (n = 1 \/ n > 1) as [H6 | H6] by lia; try (exists 1; lia). clear H1. rename H6 into H1. 
    assert (a <> 0 /\ b <> 0) as [H6 H7].
    {
      split.
        - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rmult_0_l in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_l in H4. 
          apply eq_IZR_R0 in H4. lia.
        - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_r in H4.
          apply eq_IZR_R0 in H4. lia.
    }
    assert (b = 1 \/ b = -1 \/ (b < -1 \/ b > 1)) as [H8 | [H8 | [H8 | H8]]] by lia; try (exists a; lia).
    -- assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H9 | [H9 | [H9 | H9]]] by lia; try lia.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_neg a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_neg b H8) as [l3 [H14 H15]]. 
         assert (H16 : -a > 1) by lia. clear H9. rename H16 into H9. assert (H16 : -b > 1) by lia. clear H8. rename H16 into H8.
         pose proof (z_square_even_primes (-a) H9) as [l4 [H16 [H17 H18]]]. replace ((-a)^2) with (a^2) in H17 by lia.
         pose proof (z_square_even_primes (-b) H8) as [l5 [H19 [H20 H21]]]. replace ((-b)^2) with (b^2) in H20 by lia.
         rewrite H20 in H5. rewrite H17 in H5. clear H17 H20. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5.
         assert (H22 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H22 H16 eq_refl H5) as H23.
         rewrite count_occ_app in H23. assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H24 by (rewrite H23; auto).
         apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H24; auto.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_pos a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_neg b H8) as [l3 [H14 H15]]. 
         assert (H16 : -b > 1) by lia. clear H8. rename H16 into H8. pose proof (z_square_even_primes (-b) H8) as [l4 [H16 [H17 H18]]].
         pose proof (z_square_even_primes a H9) as [l5 [H19 [H20 H21]]]. rewrite H20 in H5. clear H20 H15.
         replace ((-b)^2) with (b^2) in H17 by lia. rewrite H17 in H5. clear H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H17 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l4) l5 (fold_right Z.mul 1 (l1 ++ l4)) p H17 H19 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l4 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l4 p) in H23; auto.
    -- assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H9 | [H9 | [H9 | H9]]] by lia; try lia.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_neg a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_pos b H8) as [l3 [H14 H15]]. 
         assert (H16 : -a > 1) by lia. clear H9. rename H16 into H9. pose proof (z_square_even_primes (-a) H9) as [l4 [H16 [H17 H18]]].
         pose proof (z_square_even_primes b H8) as [l5 [H19 [H20 H21]]]. rewrite H20 in H5. clear H20 H13.
         replace ((-a)^2) with (a^2) in H17 by lia. rewrite H17 in H5. clear H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H17 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H17 H16 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H23; auto.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_pos a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_pos b H8) as [l3 [H14 H15]]. 
         pose proof (z_square_even_primes a H9) as [l4 [H16 [H17 H18]]]. pose proof (z_square_even_primes b H8) as [l5 [H19 [H20 H21]]].
         rewrite H20 in H5. rewrite H17 in H5. clear H20 H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H20 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H20 H16 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H23; auto.
Qed.

Open Scope R_scope.

Lemma Rpower_gt_0 : forall r n,
  r > 0 -> Rpower r n > 0.
Proof.
  intros r n H1. unfold Rpower. destruct (Rle_dec 0 r).
  - apply exp_pos.
  - apply exp_pos.
Qed.

Lemma Rpow_neq_0 : forall r n,
  r <> 0 -> r ^ n <> 0.
Proof.
  intros r n H1. induction n as [| n' IH].
  - simpl. nra.
  - simpl. nra.
Qed.

Lemma Rpow_div_l : forall r1 r2 k,
  r2 <> 0 -> r2 <> 0 -> (r1 / r2) ^ k = r1 ^ k / r2 ^ k.
Proof.
  intros r1 r2 k H1 H2. induction k as [| k' IH].
  - simpl. field.
  - simpl. rewrite IH. field. split. 2 : { nra. }
    apply Rpow_neq_0. auto.
Qed.

Lemma Rpow_1_k : forall k,
  1 ^ k = 1.
Proof.
  intros k. induction k as [| k' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lra.
Qed.

Lemma pow_neg1_n_plus_1 : forall (n : nat),
  (-1) ^ (n + 1) = (-1) ^ n * (-1) ^ 1.
Proof.
  intros n.
  induction n.
  - simpl. lra.
  - simpl. rewrite IHn. lra.
Qed.

Lemma pow_neg1_n_plus_n : forall (n : nat),
  (-1)^(n+n) = (-1)^n * (-1)^n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ((-1)^(S k)) with ((-1)^k * (-1)^1) by ((simpl; lra)).
    replace ((-1)^1) with (-1) by lra.
    replace ((-1) ^ k * -1 * ((-1) ^ k * -1)) with ((-1) ^ k * (-1) ^ k) by lra.
    rewrite <- IH.
    replace ((S k + S k))%nat with (((k + k) + 1) + 1)%nat by lia.
    repeat rewrite pow_neg1_n_plus_1. lra. 
Qed.

Lemma pow_neg1_n : forall (n : nat),
  (-1)^n = 1 \/ (-1)^n = -1.
Proof.
  intros n.
  induction n as [| k IH].
  - simpl. left. lra.
  - destruct IH as [H | H].
    + right. replace (S k) with (k + 1)%nat by lia. rewrite pow_neg1_n_plus_1. rewrite H. lra.
    + left. replace (S k) with (k + 1)%nat by lia. rewrite pow_neg1_n_plus_1. rewrite H. lra.
Qed.

Lemma r_mult_r_is_Rsqr : forall r : R, r * r = Rsqr r.
Proof.
  intros r.
  unfold Rsqr. reflexivity.
Qed.

Lemma pow_neg1_odd : forall k, Nat.Odd k -> (-1) ^ k = -1.
Proof.
  intros k Hodd.
  destruct Hodd as [m Heq]. rewrite Heq.
  rewrite pow_neg1_n_plus_1. simpl.
  replace ((m + (m + 0))%nat) with (m + m)%nat by lia.
  rewrite Rmult_1_r. rewrite pow_neg1_n_plus_n. 
  rewrite r_mult_r_is_Rsqr. assert (H : (0 <= ((-1) ^ m)²)) by apply Rle_0_sqr.
  destruct (pow_neg1_n m) as [Hpos | Hneg].
  - rewrite Hpos. unfold Rsqr. lra.
  - rewrite Hneg. unfold Rsqr. lra.
Qed.

Lemma pow_neg1_even : forall k, Nat.Even k -> (-1) ^ k = 1.
Proof.
  intros k. unfold Nat.Even. intros [m Heq].
  assert (H2: (-1) ^ (2 * m + 1) = -1).
  { apply pow_neg1_odd. exists m. reflexivity. } 
  rewrite Heq. rewrite pow_neg1_n_plus_1 in H2. lra.
Qed.

Lemma mult_IZR_eq_1 : forall z1 z2,
  IZR z1 * IZR z2 = 1 -> ((z1 = 1 /\ z2 = 1) \/ (z1 = -1 /\ z2 = -1))%Z.
Proof.
  intros z1 z2 H1. assert (z1 = 0 \/ z1 = 1 \/ z1 = -1 \/ z1 < -1 \/ z1 > 1)%Z as [H2 | [H2 | [H2 | [H2 | H2]]]] by lia.
  - rewrite H2 in H1. lra.
  - rewrite H2 in H1. rewrite Rmult_1_l in H1. apply eq_IZR in H1. lia.
  - rewrite H2 in H1. simpl in H1. assert (IZR z2 = -1) as H3 by lra. apply eq_IZR in H3. lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma mult_IZR_eq_neg1 : forall z1 z2,
  IZR z1 * IZR z2 = -1 -> ((z1 = 1 /\ z2 = -1) \/ (z1 = -1 /\ z2 = 1))%Z.
Proof.
  intros z1 z2 H1. assert (z1 = 0 \/ z1 = 1 \/ z1 = -1 \/ z1 < -1 \/ z1 > 1)%Z as [H2 | [H2 | [H2 | [H2 | H2]]]] by lia.
  - rewrite H2 in H1. lra.
  - rewrite H2 in H1. rewrite Rmult_1_l in H1. apply eq_IZR in H1. lia.
  - rewrite H2 in H1. simpl in H1. assert (IZR z2 = 1) as H3 by lra. apply eq_IZR in H3. lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Close Scope R_scope.

Lemma Zmult_eq_1 : forall z1 z2,
  z1 * z2 = 1 -> ((z1 = 1 /\ z2 = 1) \/ (z1 = -1 /\ z2 = -1))%Z.
Proof.
  intros z1 z2 H1. pose proof Ztrichotomy z1 0 as [H2 | [H2 | H2]]; pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma Zmult_eq_neg1 : forall z1 z2,
  z1 * z2 = -1 -> ((z1 = 1 /\ z2 = -1) \/ (z1 = -1 /\ z2 = 1))%Z.
Proof.
  intros z1 z2 H1. pose proof Ztrichotomy z1 0 as [H2 | [H2 | H2]]; pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma Even_ZEven : forall n,
  Nat.Even n <-> Z.Even (Z.of_nat n).
Proof.
  intros n; split.
  - intros [m H1]. exists (Z.of_nat m). lia.
  - intros [m H1]. exists (Z.to_nat m). lia.
Qed.

Lemma Odd_ZOdd : forall n,
  Nat.Odd n <-> Z.Odd (Z.of_nat n).
Proof.
  intros n; split.
  - intros [m H1]. exists (Z.of_nat m). lia.
  - intros [m H1]. exists (Z.to_nat m). lia.
Qed.

Search (Z.Odd).

Lemma Zpow_neg1_nat_even : forall n : nat,
  Nat.Even n -> (-1) ^ (Z.of_nat n) = 1.
Proof.
  intros n H1. apply Even_ZEven in H1. rewrite <- Z.pow_opp_even. simpl. rewrite Z.pow_1_l; lia. auto.
Qed.

Lemma Zpow_neg1_nat_odd : forall n : nat,
  Nat.Odd n -> (-1) ^ (Z.of_nat n) = -1.
Proof.
  intros n H1. apply Odd_ZOdd in H1. rewrite Z.pow_opp_odd with (a := 1). rewrite Z.pow_1_l; lia. auto.
Qed.

Lemma Zpow_neg_nat_odd : forall n z ,
  Nat.Odd n -> (-z) ^ (Z.of_nat n) = -z ^ (Z.of_nat n).
Proof.
  intros n z H1. apply Odd_ZOdd in H1. rewrite Z.pow_opp_odd with (a := z). reflexivity. auto.
Qed.

Lemma Zpow_neg_nat_even : forall n z,
  Nat.Even n -> (-z) ^ (Z.of_nat n) = z ^ (Z.of_nat n).
Proof.
  intros n z H1. apply Even_ZEven in H1. rewrite Z.pow_opp_even. reflexivity. auto.
Qed.

Lemma lemma_2_17_c : forall n k,
  (n > 0)%Z -> (k > 0)%nat -> 
  ((~exists m, (n = m^Z.of_nat k)%Z) -> irrational (Rpower (IZR n) (1 / INR k))).
Proof.
  intros n k H1 H2 H3. unfold not in *. intros [a [b H4]]. apply H3.
  assert (Rpower (IZR n) (1 / INR k) ^ k = (IZR a / IZR b) ^ k)%R as H5 by (rewrite H4; reflexivity).
  assert (n = 1 \/ n > 1)%Z as [H0 | H0] by lia.
  exists 1. rewrite Z.pow_1_l; lia.
  assert (a <> 0 /\ b <> 0) as [H6 H7].
  {
    split.
    - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rmult_0_l in H4. 
      assert (Rpower (IZR n) (1 * / INR k) > 0)%R by (apply Rpower_gt_0; apply IZR_lt; lia). lra.
    - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4.
      assert (Rpower (IZR n) (1 * / INR k) > 0)%R by (apply Rpower_gt_0; apply IZR_lt; lia). lra.
  }
  assert (IZR n * IZR b ^ k = IZR a ^ k)%R as H8.
  {
    rewrite <- Rpower_pow in H5. 2 : { apply Rpower_gt_0. apply IZR_lt. lia. }
    rewrite Rpower_mult in H5. replace (1 / INR k * INR k)%R with 1%R in H5. 2 : { field. apply not_0_INR. lia. }
    rewrite Rpower_1 in H5. 2 : { apply IZR_lt. lia. } rewrite Rpow_div_l in H5. 2 : { apply not_0_IZR. lia. }
    2 : { apply not_0_IZR. lia. } rewrite H5. field. apply Rpow_neq_0. apply not_0_IZR. lia.
  }
  rewrite pow_IZR in H8. rewrite <- mult_IZR in H8. rewrite pow_IZR in H8. apply eq_IZR in H8.
  assert (b = 1 \/ b = -1 \/ (b < -1 \/ b > 1)) as [H9 | [H9 | [H9 | H9]]] by lia.
  - rewrite H9 in H8. rewrite Z.pow_1_l in H8. exists a. lia. lia. 
  - rewrite H9 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H10 | H11] by apply lemma_2_8.
    + exists a. rewrite Zpow_neg1_nat_even in H8; auto. lia.
    + assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H12 | [H12 | [H12 | H12]]] by lia.
      * rewrite H12 in H8. exists (-1). rewrite Zpow_neg1_nat_odd in *; auto. rewrite Z.pow_1_l in H8; lia.
      * rewrite H12 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. lia.
      * exists (-a). rewrite Zpow_neg1_nat_odd in H8; auto. rewrite Z.pow_opp_odd. 2 : { apply Odd_ZOdd; auto. } lia.
      * exists (-a). rewrite Zpow_neg1_nat_odd in H8; auto. rewrite Z.pow_opp_odd. 2 : { apply Odd_ZOdd; auto. } lia.
  - assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H10 | [H10 | [H10 | H10]]] by lia.
    + rewrite H10 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Z.pow_1_l in H8; try lia. apply Zmult_eq_1 in H8 as [[H11 H12] | [H11 H12]]; lia.
    + rewrite H10 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H11 | H12] by apply lemma_2_8.
      * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_even in H8; auto. apply Zmult_eq_1 in H8 as [[H13 H14] | H13]; lia.
      * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. apply Zmult_eq_neg1 in H8 as [[H13 H14] | H13]; lia. 
    + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_neg a H10) as [l2 [H13 H14]].
      pose proof (prime_list_product_exists_neg b H9) as [l3 [H15 H16]]. 
      assert (-a > 1) as H17 by lia. clear H10. rename H17 into H10. assert (-b > 1) as H17 by lia. clear H9. rename H17 into H9.
      pose proof (z_pow_factor_primes (-a) k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes (-b) k H9) as [l5 [H20 [H21 H22]]].
      apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. 
      assert (H23 : Nat.Even k \/ Nat.Odd k) by apply lemma_2_8. destruct H23 as [H23 | H23].
      * rewrite Zpow_neg_nat_even in H18, H21; auto. rewrite H18 in H8. rewrite H21 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8.
        assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
        rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
      * rewrite Zpow_neg_nat_odd in H18, H21; auto. assert (H24 : n * fold_right Z.mul 1 l5 = fold_right Z.mul 1 l4) by lia. clear H8. rename H24 into H8. rewrite H12 in H8.
        rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
        rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
    + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_pos a H10) as [l2 [H13 H14]].
      pose proof (prime_list_product_exists_neg b H9) as [l3 [H15 H16]]. 
      assert (-b > 1) as H17 by lia. clear H9. rename H17 into H9. pose proof (z_pow_factor_primes (-b) k H9) as [l4 [H17 [H18 H19]]].
      pose proof (z_pow_factor_primes a k H10) as [l5 [H20 [H21 H22]]]. rewrite H21 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H23 | H23] by apply lemma_2_8.
      * rewrite Zpow_neg_nat_even in H18; auto. rewrite H18 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto).
        apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22].
        pose proof (prime_factorization_unique (l1 ++ l4) l5 (fold_right Z.mul 1 (l1 ++ l4)) p H24 H20 eq_refl) as H25. exists (q2 - q1)%nat. rewrite count_occ_app in H25. nia.
      * rewrite Zpow_neg_nat_odd in H18; auto. assert (H24 : n * fold_right Z.mul 1 l4 = -fold_right Z.mul 1 l5) by lia. clear H8. rename H24 into H8. rewrite H12 in H8.
        rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto). pose proof (prime_list_fold_right_pos (l1 ++ l4) H24) as H25.
        pose proof (prime_list_fold_right_pos l5 H20) as H26. nia.
    - assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H10 | [H10 | [H10 | H10]]] by lia.
      + rewrite H10 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Z.pow_1_l in H8; try lia.
      + rewrite H10 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H11 | H12] by apply lemma_2_8.
        * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_even in H8; auto. apply Zmult_eq_1 in H8 as [[H13 H14] | H13]; lia.
        * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. apply Zmult_eq_neg1 in H8 as [[H13 H14] | H13]; lia. 
      + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_neg a H10) as [l2 [H13 H14]].
        pose proof (prime_list_product_exists_pos b H9) as [l3 [H15 H16]]. 
        assert (-a > 1) as H17 by lia. clear H10. rename H17 into H10.
        pose proof (z_pow_factor_primes (-a) k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes b k H9) as [l5 [H20 [H21 H22]]].
        apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. 
        assert (Nat.Even k \/ Nat.Odd k) as [H23 | H23] by apply lemma_2_8.
        * rewrite Zpow_neg_nat_even in H18; auto. rewrite H18 in H8. rewrite H21 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8.
          assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
          rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
        * rewrite Zpow_neg_nat_odd in H18; auto. assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_list_fold_right_pos (l1 ++ l5) H24) as H25.
          pose proof (prime_list_fold_right_pos l4 H17) as H26. nia.
      + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_pos a H10) as [l2 [H13 H14]]. 
        pose proof (prime_list_product_exists_pos b H9) as [l3 [H15 H16]]. apply count_occ_perfect_factor. exists l1. split; auto.
        intros p. rewrite H12 in H8. pose proof (z_pow_factor_primes a k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes b k H9) as [l5 [H20 [H21 H22]]].
        specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. rewrite H21 in H8. rewrite H18 in H8. rewrite <- fold_right_mult_app_Z in H8. 
        assert (H23 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H23 H17 eq_refl H8) as H24.
        rewrite count_occ_app in H24.  rewrite H19 in H24. rewrite H22 in H24. exists (q1 - q2)%nat. nia.
Qed.

Lemma not_perfect_square : forall z : Z,
  (exists z2, z > z2^2 /\ z < (z2+1)^2) -> ~(exists m, (z = m^2)%Z).
Proof.
  intros z H1. intros [m H2]. destruct H1 as [z2 [H3 H4]]. rewrite H2 in *. clear H2.
  destruct (Ztrichotomy m 0) as [H5 | [H5 | H5]]; destruct (Ztrichotomy z2 0) as [H6 | [H6  | H6]]; try lia.
  - assert (-m > z2) by nia. assert (-m < z2 + 1) by nia. nia.
  - assert (m > z2) by nia. assert (m < z2 + 1) by nia. nia.
Qed.

Lemma sqrt_2_irrational_prime : irrational (sqrt 2).
Proof.
  apply lemma_2_17_b; try lia. intros [m H1]. assert (H2 : exists z, 2 > z^2 /\ 2 < (z+1)^2) by (exists 1; lia).
  pose proof (not_perfect_square 2 H2) as H3. apply H3. exists m. apply H1.
Qed.

Lemma first_n_primes_prime_list : forall l,
  first_n_primes l -> prime_list l.
Proof.
  intros l [H1 [H2 H3]]. apply H2. 
Qed.

Lemma lemma_2_17_d : forall (l : list Z),
  first_n_primes l -> exists p : Z, Znt.prime' p /\ p > max_list_Z l.
Proof.
  intros l [H1 [H2 H3]]. set (N := fold_right Z.mul 1 l + 1).
  assert (N > 1) as H4 by (destruct l; apply prime_list_product_gt_1 in H2; lia).
  destruct (prime_divides N H4) as [q H5]. exists q. split.
  - apply H5.
  - destruct H5 as [H5 H6]. destruct (in_dec Z.eq_dec q l) as [H7 | H7].
    -- assert ((q | fold_right Z.mul 1 l)) as H8 by (apply fold_right_factor_divides; auto).
       unfold N in H6. pose proof (prime_no_div q (fold_right Z.mul 1 l) H5 H8 H6) as H9. lia.
    -- specialize (H3 q). tauto.
Qed.

(* we know that for every prime list there exists a prime p which is larger than every prime in the prime list
   we prove that a prime list exists of length 0(base case) suppose one exists of length k
   then we show that one exists of length S k. but how to find the next prime? we don't know where it might be
   but we know by the prior lemma that a larger one exists. then we just form a set of all the primes larger than
   max of our list this bounded below non-empty set and so has a least element. we can grab this element with well-ordering
   principle and use it to construct S k. BOO Ya!*)

Lemma gt_list_max_not_in : forall l x,
  (x > max_list_Z l)%Z -> ~(In x l).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl in H1. simpl in H2. destruct H2 as [H2 | H2].
    -- rewrite H2 in H1. lia.
    -- apply IH in H2. lia. lia.
Qed.

Lemma le_max_list_Z : forall l x z,
  x <= max_list_Z (z :: l) -> x = z \/ (x < z /\ x > max_list_Z l) \/ x <= max_list_Z l.
Proof.
  intros l x z H1. induction l as [| h l' IH].
  - simpl in *. assert (H2 : z <= 0 \/ z > 0) by lia. destruct H2.
    -- lia.
    -- lia.
  - simpl in *. assert (H2 : z <= h \/ z > h) by lia. destruct H2.
    -- simpl in H1. lia.
    -- simpl in H1. lia.
Qed.

Lemma prime_list_len : forall n,
  exists l, first_n_primes l /\ length l = n.
Proof.
  intros n. induction n as [| k IH].
  - exists []. split.
    -- repeat split; repeat constructor. intros x [H1 H2]. simpl in H2.
       rewrite -> Znt.prime_alt in H1. assert (H3 : x >= 2) by (apply Znt.prime_ge_2 in H1; lia). lia.
    -- simpl. reflexivity.
  - destruct IH as [l [H1 H2]]. destruct (lemma_2_17_d l H1) as [p [H3 H4]].
    set (E := (fun x => (Znt.prime' x /\ x > max_list_Z l)%Z)).
    assert (exists p, E p) as [p' H5]. { exists p. unfold E. split. apply H3. apply H4. }
    assert (H6 : forall z, E z -> z >= 0).
    { intros z [H6 H7]. assert (z >= 2). {rewrite Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. } lia. }
    assert (H7 : exists z, E z). { exists p'. apply H5. }
    pose proof (well_ordering_Z E H6 H7) as [z [[H8 H9] H10]].
    exists (z :: l). split.
    -- repeat split.
      + constructor. apply gt_list_max_not_in. lia. unfold first_n_primes in H1. tauto.
      + unfold prime_list. unfold first_n_primes in H1; apply Forall_cons; tauto.
      + intros x [H11 H12]. simpl. apply le_max_list_Z in H12 as [H12 | [H12 | H12]].
        * lia.
        * destruct H12 as [H12 H13]. specialize (H10 x). assert (x >= 0) as H14.
          { rewrite Znt.prime_alt in H11. apply Znt.prime_ge_2 in H11. lia. }
          assert (E x) as H15. { unfold E. split. apply H11. apply H13. }
          apply H10 in H15. 2 : { apply H14. } lia.
        * right. apply H1. split. apply H11. apply H12.
    -- simpl. lia.
Qed.

Lemma list_len_cons : forall {A : Type} h (l : list A),
  length (h :: l) = S (length l).
Proof.
  intros A h l. simpl. reflexivity.
Qed.

Lemma max_list_cons : forall l h m,
  m = max_list_Z (h :: l) -> m = h \/ m = max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH]; simpl in *; lia.
Qed.

Lemma max_list_cons_ge : forall l h m,
  m >= max_list_Z (h :: l) -> m >= h /\ m >= max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl in *. assert (m >= h /\ m >= max_list_Z l') as [H1 H2] by lia. split.
    -- lia.
    -- lia.
Qed.

Lemma max_list_ge_not_in : forall l h,
  h > 0 -> h >= max_list_Z l /\ ~ In h l -> h > max_list_Z l.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (h >= max_list_Z l') as H5. { apply max_list_cons_ge in H2 as [H2 H6]. apply IH in H4 as H7. lia. lia. }
    assert (H6 : h > max_list_Z l'). { apply IH in H4 as H6. lia. lia. }
    assert (H7 : h <> h'). { intros H7. rewrite H7 in H3. assert (In h' (h' :: l')) as H8 by apply in_eq. tauto. }
    pose proof (max_list_cons_ge l' h' h) as [H8 H9]. lia. lia.
Qed.

Lemma max_list_ge_not_in' : forall l h,
  max_list_Z l > 0 -> max_list_Z l >= h /\ ~ In h l -> max_list_Z l > h.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (max_list_Z (h' :: l') = h' \/ max_list_Z (h' :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5 in H2. assert (h' <> h) as H6.
       { intros H6. rewrite H6 in H3. assert (In h' (h' :: l')) as H7 by apply in_eq. rewrite H6 in H7. tauto. } lia.
    -- assert (max_list_Z l' >= h) as H6. { rewrite H5 in H2. tauto. }
       assert (max_list_Z l' > h) as H7. { apply IH in H4 as H7; lia; auto. }
       lia.
Qed.

Lemma max_list_Z_eq : forall l h,
  max_list_Z (h :: l) = h \/ max_list_Z (h :: l) = max_list_Z l.
Proof.
  intros l h. simpl. lia.
Qed.

Theorem list_has_len : forall (l : list Z) (a : Z),
  In a l -> (length l > 0)%nat.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. intros [H1 | H1]; lia.
Qed.

Lemma remove_one_len : forall l x,
  In x l -> length (remove_one Z.eq_dec x l) = (length l - 1)%nat.
Proof.
  intros l x H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct (Z.eq_dec h x) as [H1 | H1].
    -- lia.
    -- simpl. destruct H as [H | H]. lia. rewrite IH.
       --- assert (length l' > 0)%nat as H2. { apply list_has_len with (a := x). apply H. } lia.
       --- apply H.
Qed.

Lemma remove_one_remains : forall l x1 x2,
  In x1 l -> x1 <> x2 -> In x1 (remove_one Z.eq_dec x2 l).
Proof.
  intros l x1 x2 H. induction l as [| h l' IH].
  - inversion H.
  - simpl. intros H1. destruct (Z.eq_dec h x2) as [H2 | H2].
    -- simpl in H. destruct H as [H | H].
       --- lia.
       --- tauto.
    -- simpl. simpl in H. tauto.
Qed.

Lemma in_notin_neq : forall (l : list Z) x1 x2,
  In x1 l -> ~ (In x2 l) -> x1 <> x2.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in *. destruct H1 as [H1 | H1].
    -- rewrite H1 in H2. tauto.
    -- tauto.
Qed.

Theorem longer_list:
    forall l1 l2 : list Z,
    (forall x : Z, In x l1 -> In x l2) ->
    (exists x : Z, In x l2 /\ ~ In x l1) ->
    NoDup l1 ->
    (length l2 > length l1)%nat.
  Proof.
    intros l1 l2 H1 H2 H3. generalize dependent l2.
    induction l1 as [| h l1' IH].
    - intros l2 H4 H5. simpl in *. destruct H5 as [x H5]. assert (exists a, In a l2) as [a H6].
    { exists x. apply H5. } apply list_has_len in H6. lia.
    - intros l2 H4 [a [H5 H6]]. apply NoDup_cons_iff in H3. destruct H3 as [H3 H3'].
      specialize (IH H3' (remove_one Z.eq_dec a l2)). apply not_in_cons in H6 as [H6 H6'].
      assert (In h (remove_one Z.eq_dec a l2)) as H7.
      { apply remove_one_remains. apply (H4 h). simpl. lia. lia. }
      assert (length (remove_one Z.eq_dec a l2) > length l1')%nat as H8.
      { apply IH. intros x H8. apply remove_one_remains. apply (H4 x). simpl. tauto. 2 : { exists h. tauto. }  apply in_notin_neq with (l := l1') (x2 := a). apply H8. apply H6'. }
      rewrite remove_one_len in H8. simpl. lia. tauto.
  Qed.

Theorem pigeonhole_principle_Z : forall (l1 l2 : list Z),
  (forall x, In x l1 -> In x l2) -> (length l2 < length l1)%nat ->
    ~ NoDup l1.
Proof.
  intros l1. induction l1 as [|a l1' IH].
  - simpl. lia.
  - simpl. intros l2 H1 H2. destruct (in_dec Z.eq_dec a (l1')) as [H3 | H3].
    -- intros H4. apply NoDup_cons_iff in H4 as [H4 H5]. tauto.
    -- intros H4. apply IH with (l2 := l2).
       3 : { apply NoDup_cons_iff in H4. tauto. }
       intros x H5. specialize (H1 x). assert (a = x \/ In x l1') as H6 by tauto. tauto.
       assert (H5 : (length l2 > length l1')%nat).
       { apply longer_list. intros x H5. apply (H1 x). tauto. exists a. split. apply (H1 a).
        tauto. tauto. apply NoDup_cons_iff in H4. tauto. }
       lia.
Qed.

Definition Zseq_pos (seq : list nat) : list Z :=
  map Z.of_nat (seq).

Lemma in_Zseq_pos : forall start len x,
  let l := seq start len in
    x > 0 -> In (Z.to_nat x) (seq start len) -> In x (Zseq_pos l).
Proof.
  intros start len x l H. unfold Zseq_pos.
  rewrite in_map_iff. exists (Z.to_nat x). split. lia. auto.
Qed.

Lemma Zseq_len : forall start len,
  let l := seq start len in
    length (l) = length (Zseq_pos l).
Proof.
  intros start len. unfold Zseq_pos. rewrite map_length. reflexivity.
Qed.

Lemma in_list_1 : forall l,
  Z.of_nat (length l) > 0 -> NoDup l -> Forall (fun x => x > 0) l -> Z.of_nat (length l) = max_list_Z l -> In 1 l.
Proof.
  intros l H1 H2 H3 H4. destruct (in_dec Z.eq_dec 1 l) as [H5 | H5]. apply H5.
  set (l2 := Zseq_pos (seq 2 (Z.to_nat (max_list_Z l - 1)))). assert (~NoDup l) as H6.
  - apply pigeonhole_principle_Z with (l2 := l2).
    2 : { assert (length l2 = Z.to_nat (max_list_Z l) - 1)%nat. { unfold l2. rewrite <- Zseq_len. rewrite seq_length. lia. } lia. }
    intros x H6. apply in_Zseq_pos. rewrite Forall_forall in H3. specialize (H3 x). tauto. apply in_seq.
    replace (2 + Z.to_nat (max_list_Z l - 1))%nat with (Z.to_nat (max_list_Z l) + 1)%nat by lia. pose proof H6 as H6'. pose proof H6 as H6''.
    apply in_list_le_max in H6. rewrite Forall_forall in H3. specialize (H3 x). apply H3 in H6'. assert (~x = 1). unfold not in *. intros H7. apply H5. rewrite H7 in H6''. tauto.
    lia.
  - tauto.
Qed.

Lemma list_len_lt_max : forall l,
  Forall (fun x => x > 1) l /\ NoDup l -> Z.of_nat (length l) <= max_list_Z l.
Proof.
  intros l. induction l as [| h l' IH].
  - intros [H1 H2]. simpl. lia.
  - intros [H1 H2]. apply Forall_cons_iff in H1 as [H1 H1']. apply NoDup_cons_iff in H2 as [H2 H3].
    assert (Z.of_nat(length l') <= max_list_Z l') as H4 by (apply IH; split; auto).
    rewrite list_len_cons. assert (max_list_Z (h :: l') = h \/ max_list_Z (h :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5. assert (H6 : h >= max_list_Z l') by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in l' h) as H7. assert (H8 : h > 0) by lia. apply H7 in H8. lia. auto.
    -- rewrite H5. assert (H6 : max_list_Z l' >= h) by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in' l' h) as H7. assert (H8 : max_list_Z l' > 0) by lia. apply H7 in H8. 2 : { tauto. }
       assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H9 | H9].
       --- lia.
       --- rewrite <- H5 in H9. assert (NoDup (h :: l')) as H10 by (apply NoDup_cons; auto).
           assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H11 | H11] by lia.
           2 : { lia. } apply in_list_1 in H11.
           + rewrite Forall_forall in H1'. specialize (H1' 1). apply H1' in H11. lia.
           + lia.
           + apply H3.
           + assert (H12 : Forall (fun x : Z => x > 1) l' -> Forall (fun x : Z => x > 0) l').
             { intros H12. rewrite Forall_forall in H12. rewrite Forall_forall. intros x H13. apply H12 in H13. lia. }
             tauto.
      --- lia.
Qed.

Lemma max_primes_ge_len : forall l,
  first_n_primes l -> max_list_Z l >= Z.of_nat (length l).
Proof.
  intros l H1. pose proof Znt.prime_ge_2 as H2.
  pose proof (Znt.not_prime_1) as H3. assert (H4 : ~ In 1 l).
  { intros H4. unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5.
    rewrite Forall_forall in H5. specialize (H5 1). apply H5 in H4. rewrite Znt.prime_alt in H4. tauto. }
  unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5. rewrite Forall_forall in H5.
  apply Z.le_ge. apply list_len_lt_max. split. rewrite Forall_forall. intros x H7. specialize (H5 x). apply H5 in H7.
  apply Znt.prime_alt in H7. apply Znt.prime_ge_2 in H7. lia. apply H1.
Qed.

Lemma prime_in_first_n_primes : forall p,
  Znt.prime' p -> exists l, first_n_primes l /\ In p l.
Proof.
  intros p H1. pose proof (prime_list_len (Z.to_nat p)) as [l [H2 H3]].
  exists l. split.
  - apply H2.
  - apply H2. apply max_primes_ge_len in H2. rewrite H3 in H2. rewrite Z2Nat.id in H2.
    2 : { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    split. apply H1. lia.
Qed.

Lemma gt_max_gt_all : forall (l : list Z) x1 x2,
  In x1 l -> x2 > max_list_Z l -> x2 > x1.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in H1. simpl in H2. destruct H1 as [H1 | H1].
    -- lia.
    -- apply IH. apply H1. lia.
Qed.

Theorem inf_primes : forall p1,
  Znt.prime p1 -> exists p2, Znt.prime p2 /\ p2 > p1.
Proof.
  intros p1 H1. rewrite <- Znt.prime_alt in H1. 
  apply prime_in_first_n_primes in H1 as [l [H1 H2]].
  pose proof (lemma_2_17_d l H1) as [p2 [H3 H4]]. exists p2. split.
  - rewrite Znt.prime_alt in H3. apply H3.
  - apply gt_max_gt_all with (l := l); tauto.
Qed.

Close Scope Z_scope.

Open Scope R_scope.

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

Lemma lemma_2_19 : forall n h,
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

Fixpoint Fibonacci (n : nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S (S n'' as n') => Fibonacci n' + Fibonacci n''
  end.

Lemma lemma_2_20 : forall n,
  Fibonacci n = (((1 + sqrt 5)/2)^n - ((1 - sqrt 5)/2)^n) / sqrt 5.
Proof.
  apply strong_induction_N.
  intros n IH. destruct n as [| n'].
  - simpl. lra.
  - assert (H1 : 0 < sqrt 5) by (apply sqrt_lt_R0; lra). destruct n' as [| n''].
    -- simpl. field. lra.
    -- replace (Fibonacci (S (S n''))) with (Fibonacci (S n'') + Fibonacci n'') by auto.
       rewrite IH. 2 : { lia. } rewrite IH. 2 : { lia. } apply Rmult_eq_reg_r with (r := sqrt 5). 2 : { lra. }
       replace (((((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'') / sqrt 5 + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') / sqrt 5) * sqrt 5)
       with (((((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'') + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n''))) by (field; lra).
       replace ((((1 + sqrt 5) / 2) ^ S (S n'') - ((1 - sqrt 5) / 2) ^ S (S n'')) / sqrt 5 * sqrt 5)
       with ((((1 + sqrt 5) / 2) ^ S (S n'') - ((1 - sqrt 5) / 2) ^ S (S n''))) by (field; lra).
       replace (((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'' + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n''))
       with (((1 + sqrt 5) / 2)^ S n'' + ((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ n'') by lra.
       replace (((1 + sqrt 5) / 2) ^ S n'' + ((1 + sqrt 5) / 2) ^ n'') with (((1 + sqrt 5) / 2) ^ n'' * (1 + ((1 + sqrt 5) / 2))) by (simpl; lra).
       replace (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - ((1 - sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ n'') with
       (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - (1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') by (simpl; lra).
       replace (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - (1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') with
       (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - ((1 - sqrt 5) / 2) ^ n'' * (1 + ((1 - sqrt 5) / 2))) by (simpl; lra).
       replace (1 + ((1 - sqrt 5) / 2)) with (((1 - sqrt 5) / 2)^2).
       2 : { replace (((1 - sqrt 5) / 2)^2) with ((1 - 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (1 + (1 + sqrt 5) / 2) with (((1 + sqrt 5) / 2)^2).
       2 : { replace (((1 + sqrt 5) / 2)^2) with ((1 + 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (((1 + sqrt 5) / 2) ^ n'' * ((1 + sqrt 5) / 2) ^ 2) with (((1 + sqrt 5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       replace (((1 - sqrt 5) / 2) ^ n'' * ((1 - sqrt 5) / 2) ^ 2) with (((1 - sqrt 5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       field.
Qed.

Definition prod_f (s n : nat) (f:nat -> R) : R :=
  prod_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma prod_f_n_n : forall n f,
  prod_f n n f = f n.
Proof.
  intros n f. unfold prod_f. replace (n - n)%nat with 0%nat by lia.
  simpl. reflexivity. 
Qed.

Definition pos_list (l : list R) : Prop :=
  Forall (fun x => x > 0) l.

Definition arithmetic_mean (l : list R) : R :=
  fold_right Rplus 0 l / INR (length l).

Definition geometric_mean (l : list R) : R :=
  if eq_nat_dec (length l) 0 then 0 else
  Rpower (fold_right Rmult 1 l) (1 / INR (length l)).

Lemma pos_list_cons : forall h l,
  pos_list (h :: l) -> h > 0 /\ pos_list l.
Proof.
  intros h l H1. unfold pos_list in H1. apply Forall_cons_iff in H1. tauto.
Qed.

Lemma pos_list_app_iff : forall l1 l2,
  pos_list (l1 ++ l2) <-> pos_list l1 /\ pos_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold pos_list in H1. apply Forall_app in H1 as [H1 H1']. tauto.
  - intros [H1 H2]. unfold pos_list. apply Forall_app. tauto.
Qed.

Lemma fold_right_mult_pos_list_gt_0 : forall l,
  pos_list l -> fold_right Rmult 1 l > 0.
Proof.
  intros l H1. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. apply pos_list_cons in H1 as [H1 H2]. apply IH in H2. nra.
Qed.

Lemma fold_right_plus_pos_list_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> fold_right Rplus 0 l > 0.
Proof.
  intros l H1 H2. induction l as [| h l' IH].
  - simpl in H2. lia.
  - simpl. destruct l'.
    -- simpl in *. apply pos_list_cons in H1 as [H1 H3]. nra.
    -- apply pos_list_cons in H1 as [H1 H3]. apply IH in H3. nra. simpl. lia.
Qed.

Lemma fold_right_mul_initial_val : forall l a,
  fold_right Rmult a l = a * fold_right Rmult 1 l.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma ge_le_arith_2 : forall a b,
  a > 0 -> b > 0 -> sqrt (a * b) <= (a + b) / 2.
Proof.
  intros a b H1 H2. apply Rmult_le_reg_r with (r := 2). lra.
  replace ((a + b) / 2 * 2) with (a + b) by lra. rewrite sqrt_mult; try lra.
  apply Rsqr_incr_0_var. 2 : { lra. } unfold Rsqr.
  replace (sqrt a * sqrt b * 2 * (sqrt a * sqrt b * 2)) with (4 * (sqrt a * sqrt a) * (sqrt b * sqrt b)) by lra.
  repeat rewrite sqrt_sqrt; try lra. replace ((a + b) * (a + b)) with (a * a + 2 * a * b + b * b) by lra.
  pose proof (Rtotal_order a b) as [H3 | [H4 | H5]]; try nra.
Qed.

Lemma geometric_mean_app : forall l1 l2,
  pos_list l1 -> pos_list l2 -> length l1 = length l2 ->
  geometric_mean (l1 ++ l2) = sqrt (geometric_mean l1 * geometric_mean l2).
Proof.
  intros l1 l2 H1 H2 H3. unfold geometric_mean. rewrite H3. destruct l1, l2.
  - simpl. rewrite Rmult_0_r. rewrite sqrt_0. reflexivity.
  - simpl in H3; lia.
  - simpl in H3; lia.
  - simpl in *. pose proof H3 as H3'. destruct (length l2) in H3. 
    -- assert (H4 : l1 = []). { destruct l1. reflexivity. simpl in H3. lia. } rewrite H4. simpl. rewrite Rmult_1_r. assert (length l2 = 0%nat). { destruct l2. auto. inversion H3'. apply length_zero_iff_nil in H4. lia. }
       rewrite H. replace (1 / (1 + 1)) with (/ 2) by nra. replace (1 / 1) with 1 by lra. rewrite Rpower_mult_distr. 2 : { apply pos_list_cons in H1. tauto. }
       2 : { assert (fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. apply fold_right_mult_pos_list_gt_0; tauto. } apply pos_list_cons in H2. nra. }
       rewrite Rpower_sqrt. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       rewrite Rpower_1. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       reflexivity.
    -- assert (H4 : length (l1 ++ r0 :: l2) = S (S (S (n + n)))).
        { replace (S (S (S (n + n)))) with (S n + S n + 1)%nat by lia. inversion H3. inversion H0. rewrite app_length. simpl. lia. }
        destruct (length (l1 ++ r0 :: l2)). lia. destruct (length l2). lia. assert (H5 : r * fold_right Rmult 1 l1 > 0). { apply pos_list_cons in H1. assert (fold_right Rmult 1 l1 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. }
        assert (H6 : r0 * fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. } rewrite Rpower_mult_distr; auto.
        rewrite <- Rpower_sqrt. rewrite Rpower_mult. rewrite H4. inversion H4 as [H7]. replace (S n1) with (S n). 2 : { inversion H3. inversion H3'. reflexivity. } repeat rewrite S_INR. rewrite plus_INR.
        replace ((1 / (INR n + 1 + 1) * / 2)) with ((1 / (INR n + INR n + 1 + 1 + 1 + 1))). 2 : { field. split; pose proof pos_INR n; lra. }
        replace (r * fold_right Rmult 1 (l1 ++ r0 :: l2)) with (r * fold_right Rmult 1 l1 * (r0 * fold_right Rmult 1 l2)).
        2 : { rewrite fold_right_app. simpl. rewrite fold_right_mul_initial_val with (a := r0 * fold_right Rmult 1 l2). nra. }
        reflexivity.
        apply Rgt_lt. apply Rpower_gt_0. apply Rmult_gt_0_compat; auto.
Qed.

Lemma pow_2_n_gt_0 : forall n,
  (2 ^ n > 0)%nat.
Proof.
  intros n. induction n as [| k IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma fold_right_plus_app : forall l1 l2,
  fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma fold_right_mult_app_R : forall l1 l2,
  fold_right Rmult 1 (l1 ++ l2) = fold_right Rmult 1 l1 * fold_right Rmult 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma lemma_2_22_b : forall (l : list R) k,
  pos_list l ->
    (length l = 2 ^ k)%nat -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l k H1 H2. generalize dependent l. induction k as [| k IH].
  - intros l H1 H2. simpl in H2. unfold geometric_mean, arithmetic_mean. rewrite H2.
    simpl. replace (1 / 1) with 1 by lra. rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0. apply H1. } 
    replace (fold_right Rplus 0 l / 1) with (fold_right Rplus 0 l) by lra. assert (H3 : exists a, l = [a]). 
    { destruct l. inversion H2. exists r. inversion H2 as [H3]. apply length_zero_iff_nil in H3. rewrite H3. reflexivity. }
    destruct H3 as [a H3]. rewrite H3. simpl. nra.
  - intros l H1 H2. set (l1 := firstn (length l / 2) l). set (l2 := skipn (length l / 2) l).
    assert (H3 : l1 ++ l2 = l). { unfold l1, l2. rewrite firstn_skipn. reflexivity. }
    assert (H4 : (length l1 = 2 ^ k)%nat).
    { unfold l1. rewrite H2. replace (2 ^ S k)%nat with (2 * 2 ^ k)%nat. 2 : { simpl. lia. }
      rewrite Nat.mul_comm. rewrite Nat.div_mul. 2 : { lia. } rewrite firstn_length. rewrite H2. 
      simpl. lia. }
    assert (H5 : (length l2 = 2^k)%nat).
    { unfold l2. rewrite H2. replace (2^S k)%nat with (2 * 2^k)%nat by (simpl; lia).
      rewrite Nat.mul_comm. rewrite Nat.div_mul by lia. rewrite skipn_length. rewrite H2.
      simpl. lia. }
    rewrite <- H3 at 1. rewrite geometric_mean_app. 2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { lia. }
    assert (H6 : (0 < length l1)%nat). { rewrite H4. apply pow_2_n_gt_0. }
    assert (H7 : (0 < length l2)%nat). { rewrite H5. apply pow_2_n_gt_0. }
    assert (pos_list l1 /\ pos_list l2) as [H8 H9]. { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    assert (H10 : sqrt (geometric_mean l1 * geometric_mean l2) <= (geometric_mean l1 + geometric_mean l2) / 2).
    { apply ge_le_arith_2. unfold geometric_mean. destruct (length l1). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto.
      unfold geometric_mean. destruct (length l2). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. }
    assert ((geometric_mean l1 <= arithmetic_mean l1) /\ (geometric_mean l2 <= arithmetic_mean l2)) as [H11 H12].
    { split; apply IH; auto. }
    assert (H13 : sqrt (geometric_mean l1 * geometric_mean l2) <= (arithmetic_mean l1 + arithmetic_mean l2) / 2) by nra.
    assert (H14 : (arithmetic_mean l1 + arithmetic_mean l2) / 2 = arithmetic_mean l).
    { unfold arithmetic_mean. replace ((fold_right Rplus 0 l1 / INR (length l1) + fold_right Rplus 0 l2 / INR (length l2)) / 2) with
      ((fold_right Rplus 0 l1 + fold_right Rplus 0 l2) / (2 * INR (length l1))). 2 : { assert (H14 : INR (length l1) <> 0). { apply not_0_INR. nia. } 
      assert (H15 : length l1 = length l2). { nia. } rewrite <- H15. field; nra. }
    rewrite <- fold_right_plus_app. rewrite H3. rewrite H2. rewrite H4. simpl. rewrite Nat.add_0_r. 
    rewrite plus_INR. replace (2 * INR (2 ^ k)) with (INR (2 ^ k) + INR (2 ^ k)) by (simpl; lra). reflexivity. }
    nra.
Qed.

Lemma exists_pow_2_gt_n : forall n,
  exists m, (2 ^ m > n)%nat.
Proof.
  intros n. induction n as [| n' IH].
  - exists 1%nat. simpl. lia.
  - destruct IH as [m IH]. exists (S m). simpl. lia.
Qed.

Lemma pos_list_arith_mean_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> arithmetic_mean l > 0.
Proof.
  intros l H1 H2. unfold arithmetic_mean. apply Rdiv_lt_0_compat. apply Rgt_lt.
  apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. auto.
Qed.

Lemma pos_list_repeat : forall a n,
  a > 0 -> pos_list (repeat a n).
Proof.
  intros a n H1. unfold pos_list. apply Forall_forall. intros x H2. apply repeat_spec in H2. lra.
Qed.

Lemma fold_right_plus_repeat : forall a n,
  fold_right Rplus 0 (repeat a n) = a * INR n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. destruct k; simpl; lra.
Qed.

Lemma fold_right_mult_repeat : forall a n,
  fold_right Rmult 1 (repeat a n) = a ^ n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma pow_minus : forall a b c,
  a > 0 -> (b > 0)%nat -> (c > 0)%nat -> (b >= c)%nat -> a ^ (b - c) = a ^ b / a ^ c.
Proof.
  intros a b c H1 H2 H3 H4. induction c as [| c' IH].
  - simpl. unfold Rdiv. rewrite Rinv_1. rewrite Rmult_1_r. rewrite Nat.sub_0_r. reflexivity.
  - simpl. replace (a^b / (a * a^c')) with (a^b / a^c' * / a). 2 : { field. split. apply pow_nonzero. lra. lra. }
    assert (c' = 0 \/ c' > 0)%nat as [H5 | H5] by lia.
    -- rewrite H5. simpl. unfold Rdiv. rewrite Rinv_1. rewrite Rmult_1_r. destruct b.
      --- lia.
      --- simpl. rewrite Nat.sub_0_r. field. lra.
    -- rewrite <- IH. 2 : { lia. } 2 : { lia. } replace (b - c')%nat with (S (b - S c'))%nat by lia. simpl. field. lra.
Qed.

Lemma Rle_pow_base : forall a b n,
  0 < a -> 0 < b -> (n > 0)%nat -> a^n <= b^n -> a <= b.
Proof.
  intros a b n H1 H2 H3 H4. induction n as [| k IH].
  - lia.
  - simpl in H4. destruct k.
    -- simpl in H4. lra.
    -- apply IH. lia. simpl. simpl in H4. pose proof Rtotal_order a b as [H5 | [H6 | H7]].
      --- assert (H6 : a^k <= b^k). { apply pow_incr. lra. } assert (H7 : a^k > 0). { apply pow_lt. lra. } nra.
      --- rewrite H6. lra.
      --- assert (H8 : b^k <= a^k). { apply pow_incr. lra. } assert (H9 : b^k > 0). { apply pow_lt. lra. }
          assert (H10 : a * a^k > b * b^k). { nra. } assert (H11 : a * (a * a^k) > b * (b * b^k)). { apply Rmult_gt_0_lt_compat. nra. nra. nra. nra. } nra.
Qed.

Lemma lemma_2_22_c : forall (l : list R),
  pos_list l -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l H1. pose proof exists_pow_2_gt_n (length l) as [m H2]. 
  set (l2 := repeat (arithmetic_mean l) (2^m - length l)). set (l3 := l ++ l2).
  assert (length l = 0 \/ length l > 0)%nat as [H3 | H3] by lia.
  - unfold geometric_mean, arithmetic_mean. apply length_zero_iff_nil in H3. rewrite H3. simpl. lra.
  - assert (H4 : arithmetic_mean l > 0). { apply pos_list_arith_mean_gt_0; auto. }
    assert (H5 : pos_list l2). { unfold l2. apply pos_list_repeat. apply H4. }
    assert (H6 : pos_list l3). { unfold l3. apply pos_list_app_iff. split; auto. }
    assert (H7 : (length l3 = 2 ^ m)%nat). { unfold l3, l2. rewrite app_length. rewrite repeat_length. lia. }
    assert (H8 : (length l3 > 0)%nat). { rewrite H7. apply pow_2_n_gt_0. }
    assert (H9 : geometric_mean l3 <= arithmetic_mean l3). { apply lemma_2_22_b with (k := m); auto. }
    unfold geometric_mean, arithmetic_mean in H9. destruct (Nat.eq_dec (length l3) 0) as [H10 | H10].
    -- lia.
    -- rewrite H7 in H9. pose proof Rle_Rpower_l (Rpower (fold_right Rmult 1 l3) (1 / INR (2 ^ m))) (fold_right Rplus 0 l3 / INR (2 ^ m)) (INR 2^m) as H11.
       assert (H12 : 0 <= INR 2 ^ m).
       { replace (INR 2) with 2 by (simpl; lra). assert (0 <= 2^m)%nat by lia. apply le_INR in H. 
         replace (INR 0) with 0 in H by (simpl; lra). replace (INR (2^m)) with (2^m) in H. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. } lra. }
       apply H11 in H12. 2 : { split. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. auto. }
       rewrite Rpower_mult in H12. replace (1 / INR (2 ^ m) * INR (2)^m) with 1 in H12. 2 : { rewrite <- pow_INR. field. apply not_0_INR. lia. }
       rewrite Rpower_1 in H12. 2 : { apply Rgt_lt. apply fold_right_mult_pos_list_gt_0; auto. }
       replace (INR 2 ^ m) with (INR (2^m)) in H12. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. }
       rewrite Rpower_pow in H12. 2 : { apply Rdiv_pos_pos. apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. lia. }
       unfold l3 in H12 at 2. rewrite fold_right_plus_app in H12. replace (fold_right Rplus 0 l) with (arithmetic_mean l * INR (length l)) in H12.
       2 : { unfold arithmetic_mean. field. apply not_0_INR. lia. } replace (fold_right Rplus 0 l2) with (arithmetic_mean l * (INR (2^m) - INR (length l))) in H12.
       2 : { unfold l2. rewrite fold_right_plus_repeat. rewrite minus_INR; try lia; nra. }
       replace ((arithmetic_mean l * INR (length l) + arithmetic_mean l * (INR (2^m) - INR (length l))) / INR (2^m)) with (arithmetic_mean l) in H12.
       2 : { field. apply not_0_INR. lia. } unfold l3 in H12. rewrite fold_right_mult_app_R in H12. replace (fold_right Rmult 1 l2) with (arithmetic_mean l ^ (2^m - length l)) in H12.
       2 : { unfold l2. rewrite fold_right_mult_repeat. reflexivity. }
       assert (H13 : arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l)) = arithmetic_mean l ^ length l).
       { rewrite pow_minus. 2 : { apply pos_list_arith_mean_gt_0; auto. } 2 : { lia. } 2 : { lia. } 2 : { lia. } field; split; apply pow_nonzero; auto; try lra. }
       assert (H14 : 0 < arithmetic_mean l ^ (2 ^ m - length l)). { apply pow_lt. apply pos_list_arith_mean_gt_0; auto. }
       assert (H15 : fold_right Rmult 1 l <= arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l))). 
       { apply Rmult_le_compat_r with (r := / arithmetic_mean l ^ (2 ^ m - length l)) in H12. 2 : { apply Rlt_le. apply Rinv_pos. lra. }
         rewrite Rmult_assoc in H12. rewrite Rinv_r in H12. 2 : { lra. } unfold Rdiv in H13. rewrite H13 in H12. rewrite Rmult_1_r in H12. lra. }
       rewrite H13 in H15. unfold geometric_mean, arithmetic_mean. destruct (Nat.eq_dec (length l) 0) as [H16 | H16].
       --- lia.
       --- apply Rle_pow_base with (n := length l); auto. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto.
           rewrite <- Rpower_pow. 2 : { apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto. } rewrite Rpower_mult.
           replace (1 / INR (length l) * INR (length l)) with 1. 2 : { field. apply not_0_INR. lia. } rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0; auto. }
           unfold arithmetic_mean in H15. nra.
Qed.

Lemma lemma_2_23_a : forall (a : R) (n m : nat),
  a ^ (n + m) = a^n * a^m.    
Proof.
  intros a n m. induction n as [| k IH].
  - simpl. lra.
  - replace (a ^ (S k + m)) with (a * (a ^ (k + m))) by (simpl; lra).
    rewrite IH. replace (a ^ S k) with (a * a ^ k) by (simpl; lra). lra.
Qed.

Lemma lemma_2_23_b : forall (a : R) (n m : nat),
  (a ^ n) ^ m = a ^ (n * m).
Proof.
  intros a n m. induction m as [| k IH].
  - simpl. rewrite Nat.mul_0_r. lra.
  - simpl. rewrite IH. rewrite <- lemma_2_23_a. 
    replace (n * S k)%nat with (n + n * k)%nat by lia. reflexivity.
Qed.

Open Scope nat_scope.

Lemma lemma_2_24_a : forall a b c,
  a * (b + c) = a * b + a * c.
Proof.
  intros a b c. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. prove_equal_nat_add.
Qed.

Lemma lemma_2_24_b : forall a,
  a * 1 = a.
Proof.
  intros a. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma lemma_2_24_c : forall a b,
  a * b = b * a.
Proof.
  intros a b. induction b as [| k IH].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite <- IH. rewrite <- lemma_2_24_b with (a := a) at 2. rewrite <- lemma_2_24_a.
    simpl. reflexivity.
Qed.

Close Scope nat_scope.

Definition Inductive (A : R -> Prop) : Prop :=
  A 1 /\ forall r : R, A r -> A (r + 1).

Definition Natural (r : R) : Prop :=
  forall A, Inductive A -> A r.

Lemma lemma_2_25_a_i : Inductive (fun r => True).
Proof.
  split; auto.
Qed.

Lemma lemma_2_25_a_ii : Inductive (fun r => r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iii : Inductive (fun r => r <> 1 / 2 /\ r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iv : ~Inductive (fun r => r > 0 /\ r <> 5).
Proof.
  intros [[H1 H2] H3]. specialize (H3 4). nra.
Qed.

Lemma lemma_2_25_a_v : forall (A B : R -> Prop),
  Inductive A /\ Inductive B -> Inductive (fun r => A r /\ B r).
Proof.
  intros A B [[H1 H2] [H3 H4]]. split.
  - auto.
  - intros r [H5 H6]. split; auto.
Qed.

Lemma lemma_2_25_b_i : Natural 1.
Proof.
  intros A [H1 H2]. auto.
Qed.

Lemma lemma_2_25_b_ii : forall k,
  Natural k -> Natural (k + 1).
Proof.
  intros k H1 A [H2 H3]. apply H3. apply H1. split; auto.
Qed.