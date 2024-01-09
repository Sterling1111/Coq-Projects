Require Import Reals Lra Lia ZArith FunctionalExtensionality List Classical.
Import ListNotations.
From Spivak Require Import Chapter1.
Open Scope R_scope.


Theorem sum_n_nat : forall n : nat,
  sum_f 0 n (fun i => INR i) = (INR n * (INR n + 1)) / 2.
Proof.
  intros n. induction n as [| k IH].
  - rewrite sum_f_0_0. simpl. lra.
  - assert (H1 : (k = 0 \/ k > 0)%nat) by lia. destruct H1 as [H1 | H1].
    -- rewrite H1. unfold sum_f. simpl. lra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite S_INR. lra.
Qed.

Theorem sum_n_square_nat : forall n : nat,
  sum_f 0 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n. induction n as [| k IH].
  - unfold sum_f. simpl. lra.
  - assert (H1 : (k = 0 \/ k > 0)%nat) by lia. destruct H1 as [H1 | H1].
    -- rewrite H1. unfold sum_f. simpl. lra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite S_INR. lra.
Qed.

Theorem sum_n_cube_nat : forall n : nat,
  sum_f 0 n (fun i => INR i ^ 3) = (sum_f 0 n (fun i => INR i)) ^ 2.
Proof.
  induction n as [| k IH].
  - unfold sum_f. simpl. lra.
  - assert (H1 : (k = 0 \/ k > 0)%nat) by lia. destruct H1 as [H1 | H1].
    -- rewrite H1. unfold sum_f. simpl. lra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite sum_n_nat.
       rewrite sum_f_i_Sn_f. 2 : { lia. }
       repeat rewrite S_INR. rewrite sum_n_nat. lra.
Qed.

Lemma lemma_2_9 : forall (A : nat -> Prop) (n0 : nat), 
  (A n0 /\ (forall k : nat, A k -> A (S k))) ->
  forall n : nat, (n >= n0)%nat -> A n.
Proof.
  intros A n0 [H1 H2] n H3.
  induction n as [| k IH].
  - inversion H3. rewrite H in H1. apply H1.
  - assert (H4 : (n0 = S k \/ n0 < S k)%nat) by lia. destruct H4 as [H4 | H4].
    -- rewrite H4 in H1. apply H1.
    -- apply H2. apply IH. lia.
Qed.

Definition choose (n k : nat) : R :=
  if n <? k then 0 else
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

Lemma lemma_2_3 : forall n k : nat,
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

Lemma lemma_2_d : forall a b n,
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
           rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite lemma_2_3. 2 : { lia. } lra. }
           rewrite H2. rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_i_Sn_f. 2 : { lia. } replace (choose (S k) (S k)) with 1. 2 : { rewrite n_choose_n. auto. }
           replace (choose (S k) 0%nat) with 1. 2 : { rewrite n_choose_0. reflexivity. }
           repeat rewrite Rmult_1_l. replace (k - (S k - 1))%nat with 0%nat by lia. replace (S k - S k)%nat with 0%nat by lia.
           replace (b ^ 0) with 1 by auto. replace (a ^ 0) with 1 by auto. rewrite Rmult_1_l. repeat rewrite Rmult_1_r.
           replace (k - 0 + 1)%nat with (S k) by lia. replace (S k - 1)%nat with k%nat by lia. rewrite n_choose_n. rewrite Rmult_1_l. rewrite n_choose_0. 
           rewrite Rmult_1_l. replace (sum_f 0 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)) with (sum_f 0 k (fun i : nat => choose (S k) i * a ^ (S k - i) * b ^ i)).
           2 : { apply sum_f_equiv. lia. intros k0 H3. replace (S k - k0)%nat with (k - k0 + 1)%nat by lia. reflexivity. }
           nra.
Qed.

Lemma Even_or_Odd' : forall n : nat,
  Nat.Even n \/ Nat.Odd n.
Proof.
  intros n. induction n as [| k IH].
  - left. unfold Nat.Even. exists 0%nat. lia.
  - destruct IH as [IH | IH].
    -- right. unfold Nat.Odd in *. destruct IH as [k0 H]. exists (k0). lia.
    -- left. unfold Nat.Even in *. destruct IH as [k0 H]. exists (S k0). lia.
Qed.