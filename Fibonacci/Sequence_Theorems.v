From Fibonacci Require Import Sequence Completeness.
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


Lemma Monotonic_Sequence_Theorem_Decreasing' : forall (a : sequence),
  eventually_decreasing a -> bounded_below a -> convergent_sequence a.
Proof.
  intros a Hedec Hbounded.
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

  pose proof (eventually_decreasing_le a Hedec) as H_lemma.

  destruct H_lemma as [N' H_lemma].
  destruct H9 as [N H9].

  set (N'' := max N N').

  assert (H10 : forall n : nat, (n >= N'')%nat -> a n < L + eps).
  { intros n H. assert (a n <= a N). apply H_lemma. lia. apply Hdec. lia. lra. }

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


Theorem Monotonic_Sequence_Theorem : forall (a : sequence),
  monotonic_sequence a -> convergent_sequence a.
Proof.
  intros a. unfold monotonic_sequence. intros [H1 | H2].
  - apply Monotonic_Sequence_Theorem_Increasing. apply H1. apply H1.
  - apply Monotonic_Sequence_Theorem_Decreasing. apply H2. apply H2.
Qed.