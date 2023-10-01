Require Import Reals Lra Lia.

Open Scope R_scope.

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

Lemma one_div_pos : forall eps : R, eps > 0 -> (1 / eps > 0).
Proof.
  intros eps Heps. apply Rlt_gt. unfold Rdiv.
  rewrite Rmult_1_l. apply Rinv_0_lt_compat.
  apply Rgt_lt in Heps. apply Heps.
Qed.

Lemma Rge_sum_implies_gt : forall r1 r2 r3 : R,
  r1 >= 0 -> r2 > 0 -> r3 > 0 -> r1 >= r2 + r3 -> r1 > r3.
Proof.
  intros r1 r2 r3 H1 H2 H3 H4.
  apply Rge_gt_trans with (r2 + r3). apply H4.
  rewrite <- Rplus_0_r. rewrite Rplus_comm. 
  apply Rplus_gt_compat_l. apply H2.
Qed.

Lemma nat_z_relationship : forall (N : Z) (n : nat),
  (n >= Z.to_nat N)%nat -> (N <= Z.of_nat n)%Z.
Proof.
  intros N n H.
  destruct (Z_lt_le_dec N 0).
  - apply Z.le_trans with (m := 0%Z).
    --  lia.
    -- apply Z2Nat.inj_le; lia.
  - apply Z2Nat.inj_le; lia.
Qed.

Lemma Rabs_triang_3 : forall r1 r2 r3 : R,
  Rabs (r1 + r2 + r3) <= Rabs r1 + Rabs r2 + Rabs r3.
Proof.
  intros r1 r2 r3.

  assert (H1 : Rabs (r1 + r2) <= Rabs(r1) + Rabs(r2)) by apply Rabs_triang.
  assert (H2 : Rabs (r1 + r2 + r3) <= Rabs(r1 + r2) + Rabs(r3)) by apply Rabs_triang.
  apply Rplus_le_compat_r with (r := Rabs r3) in H1.
  apply Rle_trans with (r2 := Rabs (r1 + r2) + Rabs r3).
  - apply H2.
  - apply H1.
Qed.

Lemma minus_frac : forall (a b c d : R),
  (b > 0) /\ (d > 0) -> a / b - c / d = (a * d - b * c) / (b * d).
Proof.
  intros a b c d [H1 H2]. unfold Rdiv. field. lra.
Qed.

Lemma neg_frac_ge : forall (a b : R),
  a >= b -> - a <= - b.
Proof.
  intros a b H. lra. 
Qed.

Lemma frac_ge : forall (a b c d : R),
  (b > 0) /\ (d > 0) -> a * d >= b * c -> a / b >= c / d.
Proof.
  intros a b c d [H1 H2] H3. 
  apply Rmult_ge_compat_r with (r := / b) in H3.
  apply Rmult_ge_compat_l with (r := / d) in H3.
  unfold Rdiv in H3.

  replace (/ d * (a * d * / b)) with (a / b) in H3 by (field; lra).
  replace (/ d * (b * c * / b)) with (c / d) in H3 by (field; lra).
  apply H3. 

  apply Rgt_ge. replace (/ d) with (1 / d) by lra. apply one_div_pos. apply H2.

  apply Rgt_ge. replace (/ b) with (1 / b) by lra. apply one_div_pos. apply H1.
Qed.

Lemma frac_le : forall (a b c d : R),
  (b > 0) /\ (d > 0) -> a * d <= b * c -> a / b <= c / d.
Proof.
  intros a b c d [H1 H2] H3. 
  apply Rmult_le_compat_r with (r := / b) in H3.
  apply Rmult_le_compat_l with (r := / d) in H3.
  unfold Rdiv in H3.
  
  replace (/ d * (a * d * / b)) with (a / b) in H3 by (field; lra).
  replace (/ d * (b * c * / b)) with (c / d) in H3 by (field; lra).
  apply H3. 

  apply Rlt_le. replace (/ d) with (1 / d) by lra. apply one_div_pos. apply H2.

  apply Rlt_le. replace (/ b) with (1 / b) by lra. apply one_div_pos. apply H1.
Qed.

Lemma frac_gt : forall (a b c d : R),
  (b > 0) /\ (d > 0) -> a * d > b * c -> a / b > c / d.
Proof.
  intros a b c d [H1 H2] H3. 
  apply Rmult_gt_compat_r with (r := / b) in H3.
  apply Rmult_gt_compat_l with (r := / d) in H3.
  unfold Rdiv in H3.

  replace (/ d * (a * d * / b)) with (a / b) in H3 by (field; lra).
  replace (/ d * (b * c * / b)) with (c / d) in H3 by (field; lra).
  apply H3.

  replace (/ d) with (1 / d) by lra. apply one_div_pos. apply H2.

  replace (/ b) with (1 / b) by lra. apply one_div_pos. apply H1.
Qed.

Lemma frac_lt : forall (a b c d : R),
  (b > 0) /\ (d > 0) -> a * d < b * c -> a / b < c / d.
Proof.
  intros a b c d [H1 H2] H3. 
  apply Rmult_lt_compat_r with (r := / b) in H3.
  apply Rmult_lt_compat_l with (r := / d) in H3.
  unfold Rdiv in H3.

  replace (/ d * (a * d * / b)) with (a / b) in H3 by (field; lra).
  replace (/ d * (b * c * / b)) with (c / d) in H3 by (field; lra).
  apply H3.

  replace (/ d) with (1 / d) by lra. apply one_div_pos. apply H2.

  replace (/ b) with (1 / b) by lra. apply one_div_pos. apply H1.
Qed.

Lemma prod_gt_prod : forall a b c d : R, 
  a > 0 -> b > 0 -> c > 0 -> d > 0 -> a >= c -> b >= d -> a * b >= c * d.
Proof.
  intros a b c d Ha Hb Hc Hd Hac Hbd.
  apply Rmult_ge_compat. 
  - lra.
  - lra.
  - lra.
  - lra.
Qed.

Lemma pos_div_pos : forall a b:R, a > 0 -> b > 0 -> a / b > 0.
Proof.
  intros a b Ha Hb.
  unfold Rdiv. (* Unfold the division to be a multiplication by inverse *)
  apply Rmult_gt_0_compat.
  - exact Ha.
  - apply Rinv_0_lt_compat. exact Hb.
Qed.