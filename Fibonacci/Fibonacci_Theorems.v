Require Import Lia Lra FunctionalExtensionality.

From Fibonacci Require Import 
  Fibonacci_Definitions Miscellaneous_Lemmas 
  Strong_Induction Sequence_Theorems.

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
  intros n H. destruct n as [| n'] eqn:En.
  - lia.
  - replace ( (2 * S n' + 1) )%nat with ( (2 * n' + 1) + 2 )%nat by lia.
    replace ( (2 * S n' - 1) )%nat with ( (2 * n' + 1) )%nat by lia.
    replace ( (2 * S n') )%nat with ( (2 * n' + 1) + 1 )%nat by lia.

    rewrite lemma1. rewrite pow_neg1_odd.
    -- lra.
    -- exists n'. reflexivity.
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

Lemma a_converges : convergent_sequence a.
Proof.
  apply Monotonic_Sequence_Theorem_Strong. unfold monotonic_sequence_eventual.
  right. split.
  - apply a_eventually_decreasing.
  - apply a_bounded_below. 
Qed.

Lemma lemma4 : forall (n : nat),
  F(2*n+2) * F(2*n) - F(2*n+1)^2 > 0.
Proof.
  destruct n as [| n'] eqn:En.
  - simpl. lra.
  - rewrite lemma1. rewrite pow_neg1_even.
    -- lra.
    -- exists (S n'). reflexivity.
Qed.

Lemma lemma5 : forall (n : nat),
  F(2*n+3) / F(2*n+2) > F(2*n+1) / F(2*n).
Proof.
  intro n. apply frac_gt.
  - split.
    -- apply fib_n_gt_0.
    -- apply fib_n_gt_0.
  - replace ( F(2*n+3) ) with ( F(2*n+2) + F(2*n+1) ) by (rewrite fib_n_plus_3; lra).
    assert (H1: F(2*n+2) = F(2*n+1) + F(2*n)) by (apply fib_n_plus_2; lia). rewrite H1 at 2.
    repeat rewrite Rmult_plus_distr_r.
    replace ( (F(2*n+1) * F(2*n+1)) ) with ( (F(2*n+1))^2 ) by lra.
    rewrite Rmult_comm with (r1 := F(2*n+1)).
    apply Rplus_gt_compat_r. apply Rminus_gt. apply lemma4.
Qed.

Lemma b_increasing : increasing b.
Proof.
  intros n. unfold b.
  apply Rge_le. apply Rgt_ge.
  replace ( (2 * S n + 1) )%nat with ( (2*n + 3)%nat ) by lia.
  replace ( (2 * S n) )%nat with ( (2*n+2)%nat ) by lia.
  apply lemma5.
Qed.

Lemma lemma6 : forall n : nat,
  F n / F (S n) <= 1.
Proof.
  intros n. 
  assert (H1 : F (S n) >= F n) by apply fib_Sn_ge_fib_n.
  assert (H2 : F (S n) > 0) by apply fib_n_gt_0.
  apply division_inequality.
  - lra.
  - lra.
Qed.

Lemma b_bounded_above : bounded_above b.
Proof.
  exists 2. intros n. unfold b.
  destruct n as [| n'] eqn:En.
  - simpl. lra.
  - assert (H1 : F(2 * S n' + 1) = F(2 * S n') + F(2 * S n' - 1)) by (apply fib_n_plus_1; lia).
    rewrite H1.
    assert (H2 : F (2 * S n' - 1) > 0) by apply fib_n_gt_0.
    assert (H3 : F (2 * S n') > 0) by apply fib_n_gt_0.
    
    assert (H4: (F (2 * S n') + F (2 * S n' - 1)) / F (2 * S n') = 1 + F (2 * S n' - 1) / F (2 * S n')).
      { field. lra. } rewrite H4.
    replace ( (2 * S n') )%nat with ( (S (2 * S n' - 1))%nat ) at 2 by lia.
    assert (H5 : F (2 * S n' - 1) / F (S (2 * S n' - 1)) <= 1) by apply lemma6.
    lra.
Qed.

Lemma b_converges : convergent_sequence b.
Proof.
  apply Monotonic_Sequence_Theorem. unfold monotonic_sequence. left.
  split.
  - apply b_increasing.
  - apply b_bounded_above.
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

Lemma b_minus_a_neg : forall (n : nat),
  b_minus_a n < 0.
Proof.
  intros n. rewrite b_minus_a_eq.
  assert (H1 : F (2 * n) >= 1) by apply fib_n_ge_1.
  assert (H2 : F (2 * n - 1) >= 1) by apply fib_n_ge_1.
  assert (H3 : F (2 * n) * F (2 * n - 1) > 0) by (apply Rmult_gt_0_compat; lra). 
  assert (H4 : 1 / (F (2 * n) * F (2 * n - 1)) > 0) by (apply pos_div_pos; lra).
  lra.
Qed.

Lemma neg_b_minus_a_lte_one_div_n : forall (n : nat),
  (n >= 1)%nat -> - b_minus_a n <= one_div_n n.
Proof.
  intros n H. unfold one_div_n.
  rewrite b_minus_a_eq.
  replace (- (-1 / (F (2 * n) * F (2 * n - 1)))) with (1 / (F (2 * n) * F (2 * n - 1))) by lra.
  apply frac_le.
  - split.
    -- apply Rmult_gt_0_compat; apply fib_n_gt_0.
    -- apply Rlt_gt. apply lt_0_INR. lia.
  - rewrite Rmult_1_l. rewrite Rmult_1_r.
    apply Rge_le. apply fib_prod_ge_n.
Qed.

Lemma b_minus_a_le_mag_one_div_n : forall (n : nat),
  (n >= 1)%nat -> Rabs(b_minus_a n - 0) <= Rabs(one_div_n n - 0).
Proof.
  intros n H. repeat rewrite Rminus_0_r. unfold Rabs.
  assert (H1 : b_minus_a n < 0) by apply b_minus_a_neg.
  assert (H2 : one_div_n n >= 0) by apply one_div_n_pos.
  destruct (Rcase_abs (b_minus_a n)) as [H3 | H4].
  - destruct (Rcase_abs (one_div_n n)) as [H4 | H5].
    -- apply (Rlt_not_ge _ _ H4) in H2. contradiction.
    -- apply neg_b_minus_a_lte_one_div_n. apply H.
  - destruct (Rcase_abs (one_div_n n)) as [H5 | H6].
    -- apply (Rlt_not_ge _ _ H5) in H2. contradiction.
    -- apply (Rlt_not_ge _ _ H1) in H4. contradiction.
Qed.

Lemma b_minus_a_arbitrarily_small : arbitrarily_small b_minus_a.
Proof.
  unfold arbitrarily_small. unfold limit_of_sequence. intros eps H1.
  assert (H2 : exists N, forall n, (n >= N)%nat -> Rabs (one_div_n n - 0) < eps).
  { apply one_div_n_arbitrarily_small. apply H1. }
  destruct H2 as [N HN].

  exists ((N + 1)%nat). intros n Hn_ge_N.
  apply Rle_lt_trans with (r2 := Rabs (one_div_n n - 0)).
  - apply b_minus_a_le_mag_one_div_n. lia.
  - apply HN. lia.
Qed.

Lemma lim_b_minus_a_0 : limit_of_sequence b_minus_a 0.
Proof.
  apply b_minus_a_arbitrarily_small.
Qed.

Lemma a_b_same_limit : forall La Lb : R,
  (limit_of_sequence a La /\ limit_of_sequence b Lb) -> (La = Lb).
Proof.
  intros La Lb [H1 H2].
  apply two_seq_converge_to_same_limit with (a := a) (b := b).
  - apply H1.
  - apply H2.
  - unfold arbitrarily_small. replace (fun n : nat => b n - a n) with (b_minus_a).
    -- apply lim_b_minus_a_0.
    -- unfold b_minus_a. unfold b. unfold a. unfold b_minus_a. apply functional_extensionality. reflexivity.
Qed.

Lemma n_odd_imp_c_eq_a : forall (n : nat),
  Nat.Odd n -> c n = a ((n / 2 + 1)%nat).
Proof.
  intros n H1. unfold c. unfold a.
  destruct n as [| n'] eqn:En.
  - inversion H1. lia.
  - pose proof H1 as H2. destruct H1 as [k H1].
    assert ((S n' / 2 = k)%nat) by (apply odd_div_2; apply H2 || apply H1).
    assert ((S n' / 2 + 1 = k + 1)%nat) by lia.
    destruct ((S n' / 2 + 1)%nat).
    -- lia.
    -- rewrite H1. rewrite H0. replace ((2 * (k + 1))%nat) with  ((2 * k + 1 + 1)%nat) by lia.
       replace ((2 * k + 1 + 1 - 1)%nat) with ((2 * k + 1)%nat) by lia. reflexivity. 
Qed.

Lemma n_even_imp_c_eq_b : forall (n : nat),
  Nat.Even n -> c n = b ((n / 2)%nat).
Proof.
  intros n H1. unfold c. unfold b.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - pose proof H1 as H2. destruct H1 as [k H1].
    assert ((S n' / 2 = k)%nat) by (apply even_div_2; apply H2 || apply H1).
    assert ((S n' / 2 = k)%nat) by lia.
    rewrite H. rewrite H1. replace ((2 * k)%nat) with  ((2 * k + 1 - 1)%nat) by lia.
    replace ((2 * k + 1 - 1)%nat) with ((2 * k)%nat) by lia. reflexivity.
Qed.

Theorem c_has_limit : forall (L1 L2: R),
  limit_of_sequence a L1 ->
  limit_of_sequence b L2 ->
  (limit_of_sequence c L1 /\ limit_of_sequence c L2).
Proof.
  intros L1 L2 H1 H2.

  assert (H4 : L1 = L2).
  { apply a_b_same_limit. split; assumption. }

  split.

  - apply c_converges_to_L with (a := a) (b := b).
    -- apply H1.
    -- rewrite <- H4 in H2. apply H2.
    -- intros n. split; intros Hparity.
      --- apply n_even_imp_c_eq_b. apply Hparity.
      --- apply n_odd_imp_c_eq_a. apply Hparity.
  - apply c_converges_to_L with (a := a) (b := b).
    -- rewrite H4 in H1. apply H1.
    -- apply H2.
    -- intros n. split; intros Hparity.
      --- apply n_even_imp_c_eq_b. apply Hparity.
      --- apply n_odd_imp_c_eq_a. apply Hparity.
Qed.

Theorem c_convergent : convergent_sequence c.
Proof.
  assert (Ha : convergent_sequence a) by apply a_converges.
  assert (Hb : convergent_sequence b) by apply b_converges.

  destruct Ha as [La Ha], Hb as [Lb Hb].

  assert (Hc_both : limit_of_sequence c La /\ limit_of_sequence c Lb).
  { apply c_has_limit; assumption. }

  destruct Hc_both as [Hc1 Hc2].
  unfold convergent_sequence. exists La. assumption.
Qed.