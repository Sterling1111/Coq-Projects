Require Import Peano ZArith Lia QArith Reals Nat Lra Classical.

From Fibonacci Require Import 
  Completeness Fibonacci_Definitions Miscellaneous_Lemmas 
  Sequence_Definitions Strong_Induction Miscellaneous_Lemmas
  Sequence_Theorems.

Open Scope R_scope.

Lemma fib_S_S_n : forall n : nat, F (S (S n)) = F (S n) + F n.
Proof.
  intros n.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma fib_n_plus_2 : forall n : nat, F(n+2) = F(n+1) + F(n).
Proof.
  intro n. 
  replace ( (n + 1)%nat ) with ( S n )%nat by lia.
  replace ( (n + 2)%nat ) with ( S (S n) )%nat by lia.
  apply fib_S_S_n.
Qed.

Lemma fib_n_plus_1 : forall n : nat, (n > 0)%nat -> F(n+1) = F(n) + F(n-1).
Proof.
  intros n H1. destruct n as [| n'] eqn:En.
  - simpl. exfalso. apply (Nat.lt_irrefl) in H1. apply H1.
  - replace ( (S n') ) with ( (n' + 1)%nat ) by lia. 
    rewrite <- Nat.add_assoc. simpl.
    replace ( (n' + 1 - 1)%nat ) with ( n' ) by lia.
    apply fib_n_plus_2.
Qed.

Lemma fib_n_plus_3 : forall n : nat, F(n+3) = F(n+2) + F(n+1).
Proof.
  intro n. 
  replace ( (n + 2)%nat ) with ( (n + 1 + 1)%nat ) by lia.
  replace ( (n + 3)%nat ) with ( (n + 1 + 2)%nat ) by lia.
  apply fib_n_plus_2.
Qed.

Lemma fib_n_ge_1 : forall n, F n >= 1.
Proof.
  apply strong_induction.
  - simpl. lra.
  - intros n IH. destruct n.
    + simpl. lra.
    + simpl. destruct n.
      ++ lra.
      ++ assert (H1: (S n <= S (S n))%nat) by lia.
         assert (H2 : (n <= S (S n))%nat) by lia.
         assert (H3 : F (S n) >= 1) by (apply IH; lia).
         assert (H4: F n >= 1) by (apply IH; lia).
         lra.
Qed.

Lemma fib_n_gt_0 : forall n, F n > 0.
Proof.
  intros n. assert (H1 : F n >= 1) by apply fib_n_ge_1. lra.
Qed.

Lemma fib_Sn_ge_fib_n : forall n : nat,
  F (S n) >= F n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - rewrite -> fib_S_S_n.  
    assert (H1 : F (S k) > 0) by apply fib_n_gt_0.
    assert (H2 : F k > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n_ge_1_imp_fib_Sn_gt_fib_n : forall n : nat,
  (n >= 1)%nat -> F (S n) > F n.
Proof.
  intros n H. destruct n as [| n'] eqn:En.
  - lia.
  - rewrite -> fib_S_S_n. 
    assert (H1 : F (S n') > 0) by apply fib_n_gt_0.
    assert (H2 : F n' > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n1_ge_n2_imp_fib_n1_ge_fib_n2 : forall (n1 n2 : nat),
  (n1 >= n2)%nat -> F n1 >= F n2.
Proof.
  intros n1 n2 H.
  induction H.
  - lra.
  - assert (H2 : F (S m) >= F m)  by apply fib_Sn_ge_fib_n.
    lra.
Qed.

Lemma fib_n_ge_n : forall n : nat,
  F n >= INR n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ( (S k) ) with ( (k + 1)%nat ) by lia.
    destruct k as [| k'] eqn:Ek.
    -- simpl. lra.
    -- rewrite fib_n_plus_1.
       --- rewrite plus_INR. 
           assert (H1 : F (S k' - 1) >= 1) by apply fib_n_ge_1.
           replace ( (INR 1) ) with ( (1) ) by (simpl; lra). lra.
       --- lia.
Qed.
    
Lemma fib_2n_ge_fib_n : forall n : nat,
  F (2 * n) >= F n.
Proof.
  intros n. assert (H : (2 * n >= n)%nat) by lia.
  apply n1_ge_n2_imp_fib_n1_ge_fib_n2. apply H.
Qed.

Lemma fib_2n_times_fib_n_ge_n : forall n : nat,
  F (2 * n) * F (2 * n - 1) >= F n.
Proof.
  intro n. assert (H1 : F ((2 * n)%nat) > 0) by apply fib_n_gt_0.
  assert (H2 : F ((2 * n - 1)%nat) >= 1) by apply fib_n_ge_1.
  assert (H3 : F ((2 * n)%nat) >= F n) by apply fib_2n_ge_fib_n.
  apply Rmult_ge_compat_l with (r := F (2 * n)%nat) in H2.
  - rewrite Rmult_1_r in H2. lra.
  - apply Rgt_ge. apply H1. 
Qed.

Lemma fib_prod_ge_n : forall (n : nat),
  F (2 * n) * F (2 * n - 1) >= INR n.
Proof.
  intros n. 
  assert (H1 : F (2 * n) * F (2 * n - 1) >= F n) by apply fib_2n_times_fib_n_ge_n.
  assert (H2 : F n >= INR n) by apply fib_n_ge_n.
  apply Rge_trans with (r3 := INR n) in H1.
  - apply H1.
  - apply H2.
Qed.

Lemma lemma1 : forall (n : nat),
  F(n+2) * F n - (F(n+1))^2 = (-1)^n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ( ((S k + 2)%nat) ) with ( (k+3)%nat ) by lia.
    replace ( (S k) ) with ( (k+1)%nat ) by lia.
    replace ( (k + 1 + 1)%nat ) with ( (k + 2)%nat ) by lia.
    replace ( (F(k+3)) ) with ( (F(k+2) + F(k+1)) ) by (rewrite fib_n_plus_3; reflexivity).
    rewrite Rmult_plus_distr_r.
    assert (Hnew: F (k + 1) ^ 2 = F (k + 2) * F k - (-1) ^ k) by (rewrite <- IH; lra).
    clear IH. rename Hnew into IH.
    replace ( F(k+1) * F(k+1) ) with ( F(k+1)^2 ) by lra.
    rewrite IH.
    replace ( F(k+2) * F(k+1) + (F(k+2) * F k - (-1)^k) - F(k+2)^2 ) with 
            ( F(k+2) * (F k + F(k+1) - F(k+2)) - (-1)^k) by lra.
    rewrite Rplus_comm.
    replace ( F(k+1) + F k ) with ( F(k+2) ) by (rewrite <- fib_n_plus_2; reflexivity).
    rewrite pow_neg1_n_plus_1. lra.
Qed.

Lemma lemma2 : forall (n : nat), 
  (n > 0)%nat -> F(2*n+1)*F(2*n-1) - F(2*n)^2 < 0.
Proof.
  intros n H. destruct n as [| k] eqn:Ek.
  - lia.
  - replace ( (2 * S k + 1) )%nat with ( (2 * k + 1) + 2 )%nat by lia.
    replace ( (2 * S k - 1) )%nat with ( (2 * k + 1) )%nat by lia.
    replace ( (2 * S k) )%nat with ( (2 * k + 1) + 1 )%nat by lia.

    rewrite lemma1. rewrite pow_neg1_odd.
    -- lra.
    -- exists k. reflexivity.
Qed.

Lemma lemma3 : forall (n : nat),
  (n > 0)%nat -> F(2*n+2) / F(2*n+1) < F(2*n) / F(2*n-1).
Proof.
  intros n H1.
  apply frac_lt.
  - split.
    -- apply fib_n_gt_0.
    -- apply fib_n_gt_0.
  - replace ( F(2*n+2) ) with ( F(2*n+1) + F(2*n) ) by (rewrite fib_n_plus_2; lra).
    assert (H2: F(2*n+1) = F(2*n) + F(2*n-1)) by (apply fib_n_plus_1; lia). rewrite H2 at 2.
    repeat rewrite Rmult_plus_distr_r.
    replace ( (F(2*n) * F(2*n)) ) with ( (F(2*n))^2 ) by lra.
    rewrite Rmult_comm with (r1 := F(2*n)).
    apply Rplus_lt_compat_r. apply Rminus_lt. apply lemma2. apply H1.
Qed.

Lemma a_eventually_decreasing : eventually_decreasing a.
Proof.
  unfold eventually_decreasing. exists 1%nat. intros n H1. unfold a.
  destruct n as [| n'] eqn:En.
  - inversion H1.
  - apply Rle_ge. apply Rlt_le.
    replace ( (2 * S (S n'))%nat ) with ( (2 * S n' + 2)%nat ) at 1 by lia.
    replace ( (2 * S (S n') -1)%nat ) with ( (2 * (S n') + 1)%nat ) by lia.
    apply lemma3. lia.
Qed.

Lemma a_bounded_below : bounded_below a.
Proof.
  exists 0. intros n. destruct n as [| n'] eqn:En.
  - simpl. lra.
  - unfold a. assert (F (2 * S n') > 0) by apply fib_n_gt_0.
    assert (F (2 * S n' - 1) > 0) by apply fib_n_gt_0.
    apply Rlt_le. apply Rdiv_lt_0_compat; apply H || apply H0. 
Qed.
    
Lemma b_minus_a_eq : forall (n : nat), 
  b_minus_a n = -1 / (F(2*n) * F(2*n - 1)).
Proof.
  intros n. unfold b_minus_a. unfold b. unfold a. destruct n.
  - simpl. lra.
  - rewrite minus_frac. 
    -- replace ( (2 * S n + 1) )%nat with ( (2 * S n - 1 + 2))%nat by lia.
       replace ( F (2 * S n) * F (2 * S n) ) with ( (F(2 * S n)^2)) by lra.
       replace ( (2 * S n) )%nat with ( (2 * S n - 1 + 1))%nat at 3 by lia.
       rewrite lemma1.
       rewrite pow_neg1_odd.
       --- lra.
       --- exists n. lia.
    -- split.
       --- apply fib_n_gt_0.
       --- apply fib_n_gt_0.
Qed.

Lemma b_minus_a_increasing : increasing b_minus_a.
Proof.
  intros n. repeat rewrite b_minus_a_eq. 
  assert (H1 : F (2 * S n) > 0) by (apply fib_n_gt_0).
  assert (H2 : F (2 * n) > 0) by (apply fib_n_gt_0).
  assert (H3 : F (2 * S n - 1) > 0) by (apply fib_n_gt_0).
  assert (H4 : F (2 * n - 1) > 0) by (apply fib_n_gt_0).
  assert (H5 : F (2 * S n) >= F (2 * n)) by (apply n1_ge_n2_imp_fib_n1_ge_fib_n2; lia).
  assert (H6 : F (2 * S n - 1) >= F (2 * n - 1)) by (apply n1_ge_n2_imp_fib_n1_ge_fib_n2; lia).
  replace (-1 / (F (2 * n) * F (2 * n - 1))) with (- (1 / (F (2 * n) * F (2 * n - 1)) )) by lra.
  replace (-1 / (F (2 * S n) * F (2 * S n - 1))) with (- ( 1 / (F (2 * S n) * F (2 * S n - 1))) ) by lra.
  apply neg_frac_ge.
  apply frac_ge.
  - split.
    -- apply Rmult_gt_0_compat; apply H2 || apply H4.
    -- apply Rmult_gt_0_compat; apply H1 || apply H3.
  - rewrite Rmult_1_l. rewrite Rmult_1_r.
    apply prod_gt_prod. lra. lra. lra. lra. lra. lra.
Qed.

Lemma b_minus_a_bounded_below : bounded_above b_minus_a.
Proof.
  exists 0. intros n. rewrite b_minus_a_eq.
  assert (H1 : F (2 * n) > 0) by (apply fib_n_gt_0).
  assert (H2 : F (2 * n - 1) > 0) by (apply fib_n_gt_0).
  assert (H3 : F (2 * n) * F (2 * n - 1) > 0) by (apply Rmult_gt_0_compat; apply H1 || apply H2).
  replace (-1 / (F (2 * n) * F (2 * n - 1))) with (- (1 / (F (2 * n) * F (2 * n - 1)) )) by lra.
  assert (H4 : 1 / (F (2 * n) * F (2 * n - 1)) > 0) by (apply pos_div_pos; lra). lra.
Qed.

Lemma b_minus_a_monotonic : monotonic_sequence b_minus_a.
Proof.
  unfold monotonic_sequence. left. split.
  - apply b_minus_a_increasing.
  - apply b_minus_a_bounded_below.
Qed.

Lemma b_minus_a_convergent : convergent_sequence b_minus_a.
Proof.
  apply Monotonic_Sequence_Theorem.
  apply b_minus_a_monotonic.
Qed.