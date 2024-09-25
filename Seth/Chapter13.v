Require Import ZArith Lia Classical Reals Lra Classical_sets List Ensembles QArith.
Import ListNotations.
From Seth Require Export Chapter12 Sums.

Open Scope nat_scope.

Definition induction_nat := forall P : nat -> Prop,
  ((P 0 /\ (forall k : nat, P k -> P (S k))) -> forall n : nat, P n).

Lemma induction_N : induction_nat.
Proof.
  unfold induction_nat.
  intros P [H1 H2] n. induction n as [| k IH].
  - apply H1.
  - apply H2. apply IH.
Qed.

Lemma lemma_13_1 : forall (n : nat),
  sum_f 0 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  induction n as [| k IH].
  - compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH. replace (S k^2) with (k^2 + 2 * k + 1). 2 : { simpl. lia. }
    replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. repeat rewrite plus_INR. lra.
Qed.

Lemma lemma_13_1' : forall (n : nat),
  (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  intro n. set (P := fun n => (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2)).
  assert (((P 0 /\ (forall k : nat, P k -> P (S k))) -> forall n : nat, P n)) as H1.
  { apply induction_N. } assert (forall n, P n) as H2.
  {
    apply H1. split.
    - unfold P. intros H2. lia.
    - intros k IH. unfold P in IH. unfold P. intros H2. assert (k = 0 \/ (k > 0)%nat) as [H3 | H3] by lia.
      -- rewrite H3. rewrite sum_f_n_n. simpl. lra.
      -- rewrite sum_f_i_Sn_f; try lia. specialize (IH H3). rewrite IH. replace (S k^2) with (k^2 + 2 * k + 1). 2 : { simpl. lia. }
         replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. repeat rewrite plus_INR. lra.
  }
  specialize (H2 n). unfold P in H2. apply H2.
Qed.

Open Scope R_scope.

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

Lemma exists_nat_list_exists_R_list : forall (l : list nat),
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
  - assert (exists n : nat, INR n = r) as [n H8].
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