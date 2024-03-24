Require Import List ZArith Sorted NArith Lia PeanoNat.
Import ListNotations.

Open Scope Z_scope.

Fixpoint lower_bound (z : Z) (l : list Z) : nat := 
  match l with
  | [] => O
  | x :: xs => if Z_lt_dec x z then S (lower_bound z xs) else O
  end.

Fixpoint replace (z : Z) (l : list Z) (i : nat) : list Z := 
  match l with
  | [] => []
  | x :: xs => match i with
               | O => z :: xs
               | S i' => x :: (replace z xs i')
               end
  end.

Lemma lower_bound_le_length : forall z l, (lower_bound z l <= length l)%nat.
Proof.
  intros z l. induction l as [| x xs IH].
  - simpl. lia.
  - simpl. destruct (Z_lt_dec x z); lia.
Qed.

Lemma lower_bound_eq_length : forall z l x,
  Sorted Z.le l -> lower_bound z l = length l -> In x l -> x < z.
Proof.
  intros z l x H1 H2 H3. induction l as [| y ys IH].
  - inversion H3.
  - simpl in H2. destruct (Z_lt_dec y z); try lia.
    injection H2 as H2. apply Sorted_inv in H1 as [H1 H1']. 
    destruct H3 as [H3 | H3]; try lia. apply IH; auto.
Qed.

Lemma Sorted_app : forall l1 l2 l3,
  Sorted Z.le l1 -> l1 = l2 ++ l3 -> (Sorted Z.le l2 /\ Sorted Z.le l3).
Proof.
  intros l1 l2 l3 H1 H2. split.
  generalize dependent l1. induction l2 as [| h t IH].
  - intros l1 H1 H2. apply Sorted_nil.
  - intros l1 H1 H2. apply Sorted_cons.
    + apply IH with (l1 := (t ++ l3)); try reflexivity.
      rewrite H2 in H1. simpl in H1. apply Sorted_inv in H1 as [H1 H1']. apply H1.
    + rewrite H2 in H1. simpl in H1. apply Sorted_inv in H1 as [H1 H1']. destruct t as [| h' t'].
      * apply HdRel_nil.
      * apply HdRel_cons. apply HdRel_inv in H1'. auto.
  - generalize dependent l1. induction l2 as [| h t IH].
    + intros l1 H1 H2. simpl in H2. rewrite H2 in H1. apply H1.
    + intros l1 H1 H2. simpl in H2. rewrite H2 in H1. apply Sorted_inv in H1 as [H1 H1']. apply IH with (l1 := t ++ l3); try reflexivity.
      apply H1.
Qed.

Lemma Sorted_app_In : forall l1 l2 l3 x y,
  Sorted Z.le l1 -> l1 = l2 ++ l3 -> (In x l2 -> In y l3 -> x <= y).
Proof.
    intros l1 l2 l3 x y H1 H2 H3 H4. generalize dependent l1. induction l2 as [| h t IH].
    - inversion H3.
    - intros l1 H1 H2. destruct H3 as [H3 | H3].
      + rewrite H3 in H2. simpl in H2. rewrite H2 in H1.
        pose proof H1 as H5. apply Sorted_app with (l2 := x :: t) (l3 := l3) in H1 as [H1 H1']; auto.
        apply Sorted_extends in H5. 2 : { unfold Relations_1.Transitive. apply Z.le_trans. }
        apply Forall_app in H5 as [H5 H6]. rewrite Forall_forall in H6. apply H6. apply H4.
      + apply IH with (l1 := t ++ l3); auto. rewrite H2 in H1. simpl in H1. apply Sorted_inv in H1. apply H1.
Qed.

Lemma exists_app : forall l1 : list Z,
  (exists l2 l3, l1 = l2 ++ l3).
Proof.
  induction l1 as [| h t IH].
  - exists [], []. reflexivity.
  - destruct IH as [l2 [l3 IH]]. exists (h :: l2), l3. simpl. rewrite IH. reflexivity.
Qed. 

Lemma exists_app_length : forall l1 : list Z,
  (exists l2 l3 n, (n <= length l1)%nat /\ l1 = l2 ++ l3 /\ length l2 = n).
Proof.
  induction l1 as [| h t IH].
  - exists [], [], O. simpl; auto.
  - destruct IH as [l2 [l3 [n [H1 [H2 H3]]]]]. exists (h :: l2), l3, (S n). split.
    + simpl. lia.
    + split; simpl; auto. rewrite H2. reflexivity.
Qed.

Lemma firstn_In : forall (l : list Z) i x,
  (i < length l)%nat -> In (nth i l x) (firstn (S i) l).
Proof.
  intros l i x H1. generalize dependent i. induction l as [| h t IH].
  - intros i H1. inversion H1.
  - intros i H1. destruct i as [| i'].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl in H1. lia.
Qed.

Lemma skipn_eq : forall (l1 l2 l3 : list Z) n,
  l1 = l2 ++ l3 -> length l2 = n -> skipn n l1 = l3.
Proof.
  intros l1 l2 l3 n H1 H2. generalize dependent n. generalize dependent l2.
  induction l1 as [| h t IH].
  - intros. apply eq_sym in H1. apply app_eq_nil in H1 as [H1 H3]. rewrite H1 in H2. simpl in H2.
    rewrite <- H2. simpl. auto.
  - intros. destruct l2 as [| h' t'].
    + simpl in H2. rewrite <- H2. simpl. auto.
    + simpl in H1. injection H1 as H1 H3. rewrite H3. rewrite <- H2. simpl.
      rewrite skipn_app. rewrite skipn_all. simpl. replace (length t' - length t')%nat with O by lia. simpl. auto.
Qed.

Lemma skipn_In : forall (l : list Z) i1 i2 x,
  (i2 < length l)%nat -> (i1 < i2)%nat -> In (nth i2 l x) (skipn (S i1) l).
Proof.
  intros l i1 i2 x H1 H2. assert (H3 : l = firstn (S i1) l ++ skipn (S i1) l).
  { rewrite firstn_skipn. reflexivity. } 
Admitted.

Lemma Sorted_nth_le : forall l i1 i2 x,
  Sorted Z.le l -> (i1 < length l)%nat -> (i2 < length l)%nat -> (i1 < i2)%nat -> nth i1 l x <= nth i2 l x.
Proof.
  intros l i1 i2 x H1 H2 H3 H4. rewrite <- (firstn_skipn (S i1) l) in H1.
  pose proof (Sorted_app_In (firstn (S i1) l ++ skipn (S i1) l) (firstn (S i1) l) (skipn (S i1) l) (nth i1 l x) (nth i2 l x)) as H5.
  apply H5 in H1; auto. apply firstn_In; auto. apply skipn_In; auto.
Qed.

Lemma lower_bound_lt_length : forall z l i1 i2,
  Sorted Z.le l -> i1 = lower_bound z l -> (i2 < length l)%nat -> (i1 < length l)%nat ->
    ((i1 <= i2)%nat -> nth i1 l 0 <= nth i2 l 0) /\ ((i1 > i2)%nat -> nth i1 l 0 > nth i2 l 0).
Proof.
  intros z l i1 i2 H1 H2 H3 H4. split.
  - intros H5. induction l as [| h t IH].
    + inversion H4.
    + assert (i1 = i2 \/ i1 < i2)%nat as [H6 | H6] by lia.
      * rewrite H6. reflexivity.
      * clear H5. rename H6 into H5. destruct i1, i2; simpl; try lia.
        -- apply Sorted_extends in H1. 2 : { unfold Relations_1.Transitive. apply Z.le_trans. }
           rewrite Forall_forall in H1. apply H1. apply nth_In. simpl in H3. lia.
        -- apply Nat.succ_lt_mono in H5. apply Sorted_nth_le; auto. 
           ++ apply Sorted_inv in H1. apply H1.
           ++ simpl in H4. lia.
           ++ simpl in H3. lia.
  - intros H5. induction l as [| h t IH].
    + inversion H4.
    + destruct i1, i2; simpl; try lia.
      -- apply Sorted_extends in H1. 2 : { unfold Relations_1.Transitive. apply Z.le_trans. }
         rewrite Forall_forall in H1.
Admitted.

Lemma lower_bound_spec : forall z l i1 i2 x,
  Sorted Z.le l -> i1 = lower_bound z l -> (i2 < length l)%nat -> 
    ((i1 < length l)%nat -> ((i1 < i2)%nat -> nth i1 l 0 <= nth i2 l 0) /\ ((i1 >= i2)%nat -> nth i1 l 0 > nth i2 l 0)) /\
    ((i1 = length l)%nat -> In x l -> x < z) /\
    ((i1 > length l)%nat -> False).
Proof.
  intros z l i1 i2 x H1 H2 H3. pose proof (lt_eq_lt_dec (lower_bound z l) (length l)) as [[H4 | H4] | H4].
  - admit.
  - split.
Admitted.

Fixpoint LIS_helper (nums sub : list Z) : list Z := 
  match nums with
  | [] => sub
  | x :: xs => if Z_gt_dec x (last sub 0) then LIS_helper xs (sub ++ [x])
               else LIS_helper xs (replace x sub (lower_bound x sub))
  end.

Definition LIS (nums : list Z) : nat := 
  match nums with
  | [] => O
  | x :: xs => let sub := [x] in length (LIS_helper nums sub)
  end.

Compute (LIS [3; 1; 8; 2; 5; 3; 7; 101; 18; 4; 6; 9; 7; 10; 2; 3; 8; 
              11; 9; 12; 5; 13; 14; 1; 15; 0; 16; 17; 19; 20; 21; 22;
              23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36;
              37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50]).

Inductive subsequence : list Z -> list Z -> Prop :=
| sub_nil : subsequence [] []
| sub_cons : forall (x : Z) (l1 l2 : list Z), subsequence l1 l2 -> subsequence l1 (x :: l2)
| sub_cons_keep : forall (x : Z) (l1 l2 : list Z), subsequence l1 l2 -> subsequence (x :: l1) (x :: l2).

Definition increasing_subsequence (l : list Z) (sub : list Z) : Prop :=
  subsequence sub l /\ Sorted Z.lt sub.

Definition longest_increasing_subsequence (l : list Z) (sub : list Z) : Prop :=
  increasing_subsequence l sub /\ forall sub', increasing_subsequence l sub' -> (length sub' <= length sub)%nat.

Lemma hd_exists : forall (l : list Z), (length l >= 1)%nat -> exists x, hd 0 l = x.
Proof.
  intros l H1. destruct l as [| x xs].
  - simpl in H1. lia.
  - exists x. reflexivity.
Qed.

Lemma LIS_helper_not_nil : forall (l1 l2 : list Z) (x : Z),
  l2 <> [] ->
  LIS_helper l1 l2 <> [].
Proof.
  induction l1 as [| h t IH].
  - intros l2 x H1. simpl. auto.
  - intros l2 x H1. simpl.   destruct (Z_gt_dec h (last l2 0)).
    + apply (IH (l2 ++ [h]) x). intros H2. rewrite <- H2 in H1. simpl in H1. destruct l2 as [| h' t'].
      * simpl in H2. inversion H2.
      * simpl in H2. inversion H2. 
    + apply (IH (replace h l2 (lower_bound h l2)) x). intros H2. rewrite <- H2 in H1. simpl in H1. destruct l2 as [| h' t'].
      * simpl in *. contradiction.
      * simpl in H2. destruct (Z_lt_dec h' h); try lia.
        -- inversion H2.
        -- inversion H2.
Qed.

Lemma sub_at_least_as_large : forall nums sub1 sub2,
  (length nums >= 1)%nat -> sub1 = (LIS_helper nums [(hd 0 nums)]) -> increasing_subsequence nums sub2 -> (length sub2 <= length sub1)%nat.
Proof.
  intros nums sub1 sub2 H1 H2 H3. generalize dependent sub2. induction sub1 as [| x xs IH].
  - intros. pose proof (hd_exists nums H1) as [x H4]. rewrite H4 in H2.
    assert ([x] <> []) as H5. { discriminate. } pose proof (LIS_helper_not_nil nums [x] x H5) as H6.
    rewrite <- H2 in H6. contradiction.
  - intros sub2 H3. 
Qed.