From Fibonacci Require Import Completeness Miscellaneous_Lemmas.
From Fibonacci Require Export Sequence_Definitions.
Require Import Lra Classical Lia.

Lemma increasing_ge : forall (a : sequence) (n1 n2 : nat),
  increasing a -> (n1 >= n2)%nat -> a n1 >= a n2.
Proof.
  intros a n1 n2 H1 H2. unfold increasing in H1.
  induction H2.
  - lra.
  - assert (H3 : a (S m) >= a m).
    { apply Rle_ge. apply H1. }
    lra.
Qed.

Lemma decreasing_le : forall (a : sequence) (n1 n2 : nat),
  decreasing a -> (n1 >= n2)%nat -> a n1 <= a n2.
Proof.
  intros a n1 n2 H1 H2. unfold decreasing in H1.
  induction H2.
  - lra.
  - assert (H3 : a (S m) <= a m).
    { apply Rge_le. apply H1. }
    lra.
Qed.

Lemma eventually_decreasing_le : forall (a : sequence),
  eventually_decreasing a ->
    exists (N : nat),
       forall (n1 n2 : nat), (n2 >= N)%nat -> (n1 >= n2)%nat -> a n1 <= a n2.
Proof.
  intros a [N H1]. unfold eventually_decreasing in H1.
  exists N. intros n1 n2 H2. intros H3.
  induction H3.
  - lra.
  - assert (H4 : a (S m) <= a m).
    { apply Rge_le. apply H1. lia. }
    lra.
Qed.

Lemma eventually_increasing_ge : forall (a : sequence),
  eventually_increasing a ->
    exists (N : nat),
       forall (n1 n2 : nat), (n2 >= N)%nat -> (n1 >= n2)%nat -> a n1 >= a n2.
Proof.
  intros a [N H1]. unfold eventually_increasing in H1.
  exists N. intros n1 n2 H2. intros H3.
  induction H3.
  - lra.
  - assert (H4 : a (S m) >= a m).
    { apply Rle_ge. apply H1. lia. }
    lra.
Qed.

(*
  Monotonic Sequence Theorem (Increasing)

  Suppose that a is an increasing sequence and that it is bounded above. 
  Then by the completeness axiom, a has a least upper bound L. Given e > 0, 
  L - e is not an upper bound for a, so there exists a natural number N such
  that a_N > L - e. But the sequence is increasing so a_n >= a_N forall n >= N.
  So forall n >= N, a_n > L - e. Now 0 <= L - a_n < e which means that 
  |L - a_n| < e. and so lim a -> L.
*)

Lemma Monotonic_Sequence_Theorem_Increasing : forall (a : sequence),
  increasing a -> bounded_above a -> convergent_sequence a.
Proof.
  intros a H1 H2. unfold bounded_above in H2. destruct H2 as [UB H2].
  assert (H3 : is_upper_bound (fun x => exists n, a n = x) UB).
  { unfold is_upper_bound. intros x [n H3]. rewrite <- H3. apply Rge_le. apply H2. }
  assert (H4 : bound (fun x => exists n : nat, a n = x)).
  { unfold bound. exists UB. apply H3. }
  assert (H5 : {L : R | is_lub (fun x => exists n : nat, a n = x) L}).
  { apply completeness. apply H4. exists (a 0%nat). exists 0%nat. reflexivity. }
  destruct H5 as [L H5]. unfold is_lub in H5. destruct H5 as [H5 H6]. unfold is_upper_bound in H5.
  unfold convergent_sequence. exists L. intros eps H7.

  assert (H8 : ~ (is_upper_bound (fun x => exists n, a n = x) (L - eps))).
  { unfold not. intros contra. specialize (H6 (L - eps)). apply H6 in contra. lra. }
  unfold is_upper_bound in H8. unfold not in H8.

  assert (H9 : exists N : nat, a N > L - eps).
  { 
    apply not_all_not_ex. unfold not. intro H9. apply H8. intros x H10. 
    destruct H10 as [n H10]. rewrite <- H10. specialize (H9 n). 
    apply Rnot_gt_le. unfold not. apply H9.
  }
  destruct H9 as [N H9].

  assert (H10 : forall n : nat, (n >= N)%nat -> a n > L - eps).
  { intros n H. assert (a n >= a N). apply increasing_ge. apply H1. lia. lra. }
  assert (H11 : forall n : nat, (n >= N)%nat -> a n <= L).
  {  intros n H11. specialize (H5 (a n)). apply H5. exists n. reflexivity. }
  assert (H12 : forall n : nat, (n >= N)%nat -> 0 <= L - a n < eps).
  { intros n. split. 
    assert (H12 : (a n <= L) -> 0 <= L - a n). lra. apply H12. apply H11. apply H. 
    assert (H12 : (a n > L - eps) -> L - a n < eps). lra. apply H12. apply H10. apply H. }
    exists N. intros n H13. specialize (H12 n). unfold Rabs. destruct Rcase_abs.
    - replace (- (a n - L)) with (L - a n) by lra. apply H12. lia.
    - assert (H14 : a n >= L) by lra. assert (H15 : a n <= L). apply H11. lia. 
        lra.
Qed.

Lemma Monotonic_Sequence_Theorem_Decreasing : forall (a : sequence),
  decreasing a -> bounded_below a -> convergent_sequence a.
Proof.
  intros a Hdec Hbounded.
  unfold bounded_below in Hbounded.
  destruct Hbounded as [LB HLB].

  assert (H3 : is_lower_bound (fun x => exists n, a n = x) LB).
  { unfold is_lower_bound. intros x [n H3]. rewrite <- H3. apply Rle_ge. apply HLB. }

  assert (H4 : has_lower_bound (fun x => exists n : nat, a n = x)).
  { unfold has_lower_bound. exists LB. apply H3. }

  assert (H5 : {L : R | is_glb (fun x => exists n : nat, a n = x) L}).
  { apply completeness_lower_bound. apply H4. exists (a 0%nat). exists 0%nat. reflexivity. }

  destruct H5 as [L H5]. unfold is_glb in H5. destruct H5 as [H5 H6]. unfold is_lower_bound in H5.

  unfold convergent_sequence. exists L. intros eps H7.

  assert (H8 : ~ (is_lower_bound (fun x => exists n, a n = x) (L + eps))).
  { unfold not. intros contra. specialize (H6 (L + eps)). apply H6 in contra. lra. }

  unfold is_lower_bound in H8. unfold not in H8.

  assert (H9 : exists N : nat, a N < L + eps).
  { 
    apply not_all_not_ex. unfold not. intro H9. apply H8. intros x H10. 
    destruct H10 as [n H10]. rewrite <- H10. specialize (H9 n). 
    apply Rnot_lt_ge. unfold not. apply H9.
  }
  destruct H9 as [N H9].

  assert (H10 : forall n : nat, (n >= N)%nat -> a n < L + eps).
  { intros n H. assert (a n <= a N). apply decreasing_le. apply Hdec. lia. lra. }

  assert (H11 : forall n : nat, (n >= N)%nat -> a n >= L).
  {  intros n H11. specialize (H5 (a n)). apply H5. exists n. reflexivity. }

  assert (H12 : forall n : nat, (n >= N)%nat -> 0 <= a n - L < eps).
  { intros n. split. 
    assert (H12 : (a n >= L) -> 0 <= a n - L). lra. apply H12. apply H11. apply H. 
    assert (H12 : (a n < L + eps) -> a n - L < eps). lra. apply H12. apply H10. apply H. }
    
  exists N. intros n H13. specialize (H12 n). unfold R_dist.
  unfold Rabs. destruct Rcase_abs.
  - replace (- (a n - L)) with (L - a n) by lra. assert (H14 : a n >= L). apply H11. apply H13. lra.
  - apply H12. lia.
Qed.

(*
  Monotonic Sequence Theorem (Eventually Increasing)

  Suppose that a is an eventually increasing sequence that is bound above.
  Construct a set S of all the elements of a starting from the point of
  continual increase. Then this set has a least upper bound since it is bound
  above by at most the bound of sequence a. Then the proof follows the same
  as above.
*)

Lemma Monotonic_Sequence_Theorem_Increasing_Eventually : forall (a : sequence),
  eventually_increasing a -> bounded_above a -> convergent_sequence a.
Proof.
  intros a [N H1] [UB H2].
  pose (b := (fun n => a ((n + N)%nat)) : sequence).

  assert (H3 : increasing b) by (intros n; apply H1; lia).
  assert (H4 : bounded_above b) by (exists UB; intros n; apply H2).

  assert (H5 : convergent_sequence b).
  { apply Monotonic_Sequence_Theorem_Increasing. apply H3. apply H4. }

  destruct H5 as [L H5].
  exists L. intros eps.
  specialize (H5 eps).
  intros H6.
  destruct H5 as [N' H5].
  - apply H6.
  - exists (N' + N)%nat.
    intros n H7.
    specialize (H5 (n - N)%nat).
    unfold b in H5.
    replace (n - N + N)%nat with n in H5 by lia.
    apply H5. lia.
Qed.

Lemma Monotonic_Sequence_Theorem_Decreasing_Eventually : forall (a : sequence),
  eventually_decreasing a -> bounded_below a -> convergent_sequence a.
Proof.
  intros a [N H1] [LB H2].
  pose (b := (fun n => a ((n + N)%nat)) : sequence).

  assert (H : convergent_sequence b).
  { apply Monotonic_Sequence_Theorem_Decreasing; 
    [intros n; apply H1; lia | exists LB; intros n; apply H2]. }

  destruct H as [L H]. exists L.
  intros eps H6. destruct (H eps H6) as [N' H5].
  exists (N' + N)%nat.
  intros n H7. unfold b in H5. specialize (H5 ((n - N)%nat)).
  replace (n - N + N)%nat with n in H5 by lia. apply H5. lia.
Qed.

Theorem Monotonic_Sequence_Theorem : forall (a : sequence),
  monotonic_sequence a -> convergent_sequence a.
Proof.
  intros a. unfold monotonic_sequence. intros [H1 | H2].
  - apply Monotonic_Sequence_Theorem_Increasing. apply H1. apply H1.
  - apply Monotonic_Sequence_Theorem_Decreasing. apply H2. apply H2.
Qed.

Theorem Monotonic_Sequence_Theorem_Strong : forall (a : sequence),
  monotonic_sequence_eventual a -> convergent_sequence a.
Proof.
  intros a. unfold monotonic_sequence_eventual. intros [H1 | H2].
  - apply Monotonic_Sequence_Theorem_Increasing_Eventually. apply H1. apply H1.
  - apply Monotonic_Sequence_Theorem_Decreasing_Eventually. apply H2. apply H2.
Qed.

Definition one_div_n (n : nat) : R := 1 / INR n.
Definition neg_one_div_n (n : nat) : R := -1 * (one_div_n n).

Lemma one_div_n_eventually_decreasing : eventually_decreasing one_div_n.
Proof.
  unfold eventually_decreasing.
  exists 1%nat.
  intros n Hn.
  unfold one_div_n.
  induction n.
  - lia.
  - unfold Rdiv. apply Rmult_ge_compat_l.
    -- lra.
    -- apply Rle_ge. apply Rinv_le_contravar.
       --- apply lt_0_INR. lia.
       --- apply le_INR. lia.
Qed.

Lemma one_div_n_bounded_below : bounded_below one_div_n.
Proof.
  exists 0. intros n. unfold one_div_n. unfold Rdiv.
  rewrite Rmult_1_l.
  destruct n.
  - simpl. rewrite Rinv_0. lra.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Theorem one_div_n_convergent : convergent_sequence one_div_n.
Proof.
  apply Monotonic_Sequence_Theorem_Strong. unfold monotonic_sequence_eventual.
  right. split.
  - apply one_div_n_eventually_decreasing.
  - apply one_div_n_bounded_below.
Qed.

Lemma one_div_n_arbitrarily_small : arbitrarily_small one_div_n.
Proof.
  unfold arbitrarily_small. unfold limit_of_sequence. intros eps H1. unfold one_div_n.

  set (N := (up (1 + (1 / eps)))%nat).

  exists (Z.to_nat N).

  intros n H2. unfold Rabs. rewrite Rminus_0_r.
  
  destruct (Rcase_abs (1 / INR n) ) as [H3 | H3].
    - assert (H4 : 1 / INR n >= 0).
      {
        destruct n. 
        - simpl. unfold Rdiv. rewrite Rmult_1_l. apply Req_ge. apply Rinv_0.
        - apply Rgt_ge. apply one_div_pos.  rewrite S_INR. 
          apply Rlt_gt. apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1. 
      }
      apply Rlt_not_ge in H4. contradiction. apply H3.
    - assert (H4 : IZR N >= 1 + (1 / eps)).
    { 
      generalize (archimed (1 + (1 / eps))). intros [H4 H5].
      apply Rle_ge.
      - unfold N. unfold Rle. left. apply H4.
    }

    assert (H5 : INR n >= IZR N).
    {
      apply Rle_ge.
      rewrite INR_IZR_INZ.
      apply IZR_le.
      apply nat_z_relationship.
      apply H2.
    }
    assert (H6 : INR n >= 1 + (1 / eps)).
    {
      apply Rge_trans with (r2 := IZR N).
      - apply H5.
      - apply H4.
    }
    assert (H7 : 1 + 1 / eps > 0).
    {
      apply Rplus_lt_le_0_compat.
      - apply Rlt_0_1.
      - apply Rlt_le. apply one_div_pos. apply H1.
    }
    assert (H8 : IZR N > 0).
    {
      apply Rge_gt_trans with (r2 := 1 + 1 / eps).
      - apply H4.
      - apply H7.
    }
    pose proof H6 as H9.
    apply Rplus_ge_compat_l with (r := 1) in H6.
    apply Rge_sum_implies_gt in H6.
    -- apply Rplus_gt_reg_l in H6.
       unfold Rdiv. rewrite Rmult_1_l. apply Rgt_lt in H6. apply Rinv_lt_contravar in H6.
       --- unfold Rdiv in H6. rewrite Rmult_1_l in H6. rewrite Rinv_inv in H6. apply H6.
       --- apply Rgt_lt. apply Rmult_gt_0_compat.
           ---- apply one_div_pos. apply H1.
           ---- apply Rge_gt_trans with (r2 := IZR N).
                { apply H5. }
                { apply H8. }
    -- apply Rle_ge. apply Rlt_le. apply Rplus_le_lt_0_compat.
      --- apply Rlt_le. apply Rlt_0_1.
      --- apply Rge_gt_trans with (r2 := IZR N).
          { apply H5. }
          { apply H8. }
    -- apply Rlt_gt. apply Rlt_0_1.
    -- apply Rplus_lt_le_0_compat.
      --- apply Rlt_0_1.
      --- apply Rlt_le. apply one_div_pos. apply H1.
Qed.

Lemma lim_one_div_n_0 : limit_of_sequence one_div_n 0.
Proof.
  apply one_div_n_arbitrarily_small.
Qed.

Lemma two_seq_converge_to_same_limit: 
  forall (a b : sequence) (La Lb : R),
  (* Assuming a_n converges to La and b_n converges to Lb *)
  limit_of_sequence a La -> limit_of_sequence b Lb -> arbitrarily_small (fun n => a n - b n) ->
  La = Lb.
Proof.
  intros a b La Lb Ha Hb Hdiff.

  unfold limit_of_sequence in Ha, Hb.
  unfold arbitrarily_small in Hdiff. 
  unfold limit_of_sequence in Hdiff.

  set (eps := Rabs (La - Lb)).
  pose proof (Rtotal_order La Lb) as [Hlt|[Heq|Hgt]].

  - assert (Heps_pos : 0 < eps) by (apply Rabs_pos_lt; lra).
    assert (Heps_div_4_pos : eps / 4 > 0) by lra.
      
    destruct (Ha (eps / 4) Heps_div_4_pos) as [Na HNa].
    destruct (Hb (eps / 4) Heps_div_4_pos) as [Nb HNb].
    destruct (Hdiff (eps / 4) Heps_div_4_pos) as [Nc HNc].

    set (N := max (max Na Nb) Nc).
    set (n := N).

    assert (Hna : (n >= Na)%nat). lia.
    assert (Hnb : (n >= Nb)%nat). lia.
    assert (Hnc : (n >= Nc)%nat). lia.
    assert (Hnaeps : ((eps / 4) > Rabs (a n - La))). { apply HNa. apply Hna. }
    assert (Hnbeps : ((eps / 4) > Rabs (b n - Lb))). { apply HNb. apply Hnb. }
    assert (Hndeps : ((eps / 4) > Rabs (a n - b n))). { rewrite <- Rminus_0_r with (r := a n - b n). apply HNc. apply Hnc. }
    assert (Heps_eq : eps = Rabs((La - a n) + (b n - Lb) + (a n - b n))).
    { unfold eps. assert ((La - a n) + (b n - Lb) + (a n - b n) = La - Lb) by lra. rewrite H. reflexivity. }
    assert (Heps_lte : eps <= Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Heps_eq. apply Rabs_triang_3. } 
    assert (Heps_lte_eq : Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n) = Rabs (a n - La) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Rabs_minus_sym. rewrite Rabs_minus_sym with (x := a n) (y := b n). reflexivity. }

    rewrite Heps_lte_eq in Heps_lte.
    assert (Heps_lte_lt : Rabs (a n - La) + Rabs (Lb - b n) + Rabs (b n - a n) < (eps / 4) + (eps / 4) + (eps / 4)) by lra.
    replace (eps / 4 + eps / 4 + eps / 4) with (3 * eps / 4) in Heps_lte_lt by lra.
    assert (H_contra : eps < 3 * eps / 4) by lra. lra.

  - assumption.

  - assert (Heps_pos : 0 < eps) by (apply Rabs_pos_lt; lra).
    assert (Heps_div_4_pos : eps / 4 > 0) by lra.
      
    destruct (Ha (eps / 4) Heps_div_4_pos) as [Na HNa].
    destruct (Hb (eps / 4) Heps_div_4_pos) as [Nb HNb].
    destruct (Hdiff (eps / 4) Heps_div_4_pos) as [Nc HNc].

    set (N := max (max Na Nb) Nc).
    set (n := N).

    assert (Hna : (n >= Na)%nat). lia.
    assert (Hnb : (n >= Nb)%nat). lia.
    assert (Hnc : (n >= Nc)%nat). lia.
    assert (Hnaeps : ((eps / 4) > Rabs (a n - La))). { apply HNa. apply Hna. }
    assert (Hnbeps : ((eps / 4) > Rabs (b n - Lb))). { apply HNb. apply Hnb. }
    assert (Hndeps : ((eps / 4) > Rabs (a n - b n))). { rewrite <- Rminus_0_r with (r := a n - b n). apply HNc. apply Hnc. }
    assert (Heps_eq : eps = Rabs((La - a n) + (b n - Lb) + (a n - b n))).
    { unfold eps. assert ((La - a n) + (b n - Lb) + (a n - b n) = La - Lb) by lra. rewrite H. reflexivity. }
    assert (Heps_lte : eps <= Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Heps_eq. apply Rabs_triang_3. } 
    assert (Heps_lte_eq : Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n) = Rabs (a n - La) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Rabs_minus_sym. rewrite Rabs_minus_sym with (x := a n) (y := b n). reflexivity. }

    rewrite Heps_lte_eq in Heps_lte.
    assert (Heps_lte_lt : Rabs (a n - La) + Rabs (Lb - b n) + Rabs (b n - a n) < (eps / 4) + (eps / 4) + (eps / 4)) by lra.
    replace (eps / 4 + eps / 4 + eps / 4) with (3 * eps / 4) in Heps_lte_lt by lra.
    assert (H_contra : eps < 3 * eps / 4) by lra. lra.
Qed.

Lemma two_seq_arbitrarily_small_pos : forall (a b : sequence),
  arbitrarily_small b -> a_bounded_above_by_b a b -> nonnegative_sequence a -> arbitrarily_small a.
Proof.
  intros a b H1 H2 H3.
  unfold arbitrarily_small in H1. unfold limit_of_sequence in H1.
  unfold a_bounded_above_by_b in H2.
  unfold nonnegative_sequence in H3.
  unfold arbitrarily_small. unfold limit_of_sequence.
  intros eps Heps.
  destruct (H1 eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  unfold Rabs. rewrite Rminus_0_r. rewrite Rminus_0_r in HN.
  specialize (H3 n). specialize (H2 n).
  destruct (Rcase_abs (a n)) as [Hbn | Hbn].
  - lra.
  - unfold Rabs in HN. destruct (Rcase_abs (b n)) as [Hbn' | Hbn'].
    + lra.
    + lra.
Qed.

Lemma two_seq_arbitrarily_small_neg : forall (a b : sequence),
  arbitrarily_small b -> a_bounded_below_by_b a b -> nonpositive_sequence a -> arbitrarily_small a.
Proof.
  intros a b H1 H2 H3.
  unfold arbitrarily_small in H1. unfold limit_of_sequence in H1.
  unfold a_bounded_below_by_b in H2.
  unfold nonpositive_sequence in H3.
  unfold arbitrarily_small. unfold limit_of_sequence.
  intros eps Heps.
  destruct (H1 eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  unfold Rabs. rewrite Rminus_0_r. rewrite Rminus_0_r in HN.
  specialize (H3 n). specialize (H2 n).
  destruct (Rcase_abs (a n)) as [Hbn | Hbn].
  - unfold Rabs in HN. destruct (Rcase_abs (b n)) as [Hbn' | Hbn'].
    + lra.
    + lra.
  - lra.
Qed.

Lemma seq_neg_seq_arbitrarily_small : forall (a : sequence),
  arbitrarily_small a -> arbitrarily_small (fun n => - a n).
Proof.
  intros a H1.
  unfold arbitrarily_small in H1. unfold limit_of_sequence in H1.
  unfold arbitrarily_small. unfold limit_of_sequence.
  intros eps Heps.
  destruct (H1 eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  unfold Rabs. rewrite Rminus_0_r. rewrite Rminus_0_r in HN.
  replace (- - a n) with (a n) by lra.
  destruct (Rcase_abs (a n)) as [Hbn | Hbn].
  - destruct (Rcase_abs (- a n)) as [Hbn' | Hbn'].
    + lra.
    + unfold Rabs in HN. destruct (Rcase_abs (a n)) as [Hbn'' | Hbn''].
      * lra.
      * lra.
  - destruct (Rcase_abs (- a n)) as [Hbn' | Hbn'].
    + unfold Rabs in HN. destruct (Rcase_abs (a n)) as [Hbn'' | Hbn''].
      * lra.
      * lra.
    + lra.
Qed.

Lemma neg_one_div_n_arbitrarily_small : arbitrarily_small (fun n => - one_div_n n).
Proof.
  apply seq_neg_seq_arbitrarily_small.
  apply one_div_n_arbitrarily_small.
Qed.

Lemma one_div_n_pos : forall (n : nat),
  one_div_n n >= 0.
Proof.
  unfold one_div_n. destruct n. 
  - simpl. unfold Rdiv. rewrite Rmult_1_l. apply Req_ge. apply Rinv_0.
  - apply Rgt_ge. apply pos_div_pos. lra. rewrite S_INR. 
    apply Rlt_gt. apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
Qed. 

Lemma c_converges_to_L:
  forall (a b c : sequence) (L : R),
  limit_of_sequence a L ->
  limit_of_sequence b L ->
  (forall n : nat,
    (Nat.Even n -> c n = b ((n / 2)%nat)) /\
    (Nat.Odd n -> c n = a ((n / 2 + 1)%nat))) ->
  limit_of_sequence c L.
Proof.
intros a b c L Han Hbn Hcn.

unfold limit_of_sequence in Han, Hbn. unfold limit_of_sequence.
intros eps Heps.

destruct (Han eps Heps) as [Na HNa].
destruct (Hbn eps Heps) as [Nb HNb].

set(N := max (2 * Na - 1) (2 * Nb)).
exists N.

intros n Hn.

destruct (Hcn n) as [Heven1 Hodd1].

destruct (Nat.Even_or_Odd n) as [Heven2 | Hodd2].
- pose proof Heven2 as Heven3. apply Heven1 in Heven2.
  rewrite Heven2. apply HNb. destruct (Heven3) as [k H]. assert ((n / 2 = k)%nat).
  { apply even_div_2. apply Heven3. apply H. }
  assert ((2 * k) >= (N))%nat by lia. 
  assert (n >= 2 * Nb)%nat by lia. lia.
- pose proof Hodd2 as Hodd3. apply Hodd1 in Hodd2.
  rewrite Hodd2. apply HNa. destruct (Hodd3) as [k H]. assert ((n / 2 = k)%nat).
  { apply odd_div_2. apply Hodd3. apply H. } lia.
Qed.