Require Import Reals Lra Lia ZArith.ZArith Coq.Logic.FunctionalExtensionality.

Open Scope R_scope.

Lemma lemma_1_1_i : forall (a x : R),
  a <> 0 -> a * x = a -> x = 1.
Proof.
  intros a x H1 H2.
  rewrite <- Rinv_l with (r := a).
  - rewrite <- H2 at 2.
    rewrite <- Rmult_assoc.
    rewrite Rinv_l.
    -- rewrite Rmult_1_l. reflexivity.
    -- apply H1.
  - apply H1.
Qed.

Lemma lemma_1_1_ii : forall (x y : R),
  pow x 2 - pow y 2 = (x - y) * (x + y).
Proof.
  intros x y. unfold pow. unfold Rminus. repeat rewrite Rmult_1_r.
  rewrite Rmult_plus_distr_l. repeat rewrite Rmult_plus_distr_r.
  rewrite <- Rplus_assoc. rewrite Rplus_comm with (r1 := x * x + (-y * x)).
  rewrite Rplus_comm with (r1 := x * y). rewrite Rplus_assoc with (r1 := x * x).
  rewrite Rmult_comm with (r1 := -y).  rewrite <- Rmult_plus_distr_l. 
  rewrite Rplus_opp_l. rewrite Rmult_0_r. rewrite Rplus_0_r.
  rewrite <- Ropp_mult_distr_l_reverse. reflexivity.
Qed.

Lemma lemma_1_1_iii : forall (x y : R),
  x = y \/ x = -y -> pow x 2 = pow y 2.
Proof.
  intros x y H. destruct H as [H | H].
  - rewrite H. reflexivity.
  - rewrite H. unfold pow. rewrite <- Rmult_assoc. rewrite Rmult_opp_opp.
    repeat rewrite Rmult_1_r. reflexivity.
Qed.

Lemma lemma_1_1_iv : forall (x y : R),
  pow x 3 - pow y 3 = (x - y) * (pow x 2 + x * y + pow y 2).
Proof.
  intros x y. unfold pow. unfold Rminus. repeat rewrite Rmult_1_r. 
  repeat rewrite Rmult_plus_distr_l. repeat rewrite Rmult_plus_distr_r.
  rewrite Rplus_assoc with (r1 := x * (x * x)). 
  rewrite <- Rplus_assoc with (r1 := -y * (x * x)).
  rewrite Rmult_comm with (r1 := -y) (r2 := x * x).
  rewrite <- Rmult_assoc with (r2 := x) (r3 := y).
  replace (x * x * - y) with (- (x * x * y)) by lra.
  rewrite Rplus_opp_l. rewrite Rplus_0_l. 
  rewrite Rplus_assoc with (r1 := x * (x * x)).
  rewrite <- Rplus_assoc with (r1 := -y * (x * y)).
  rewrite Rmult_comm with (r1 := -y) (r2 := x * y).
  replace (x * y * - y) with (- (x * y * y)) by lra.
  rewrite Rmult_assoc with (r1 := x) at 1. rewrite Rplus_opp_l.
  rewrite Rplus_0_l. replace (-y * (y * y)) with (- (y * (y * y))) by lra.
  reflexivity.
Qed.

Fixpoint sum_from_to' (f : nat -> R) (i n : nat) : R :=
  match n with
  | O => f i
  | S n' => sum_from_to' f i n' + f ((i + S n')%nat)
  end.

Definition sum_from_to (f : nat -> R) (i n : nat) : R := 
  if (n <? i)%nat then 0 else sum_from_to' f i (n - i).

Lemma sum_from_to_ex : sum_from_to (fun i => INR i) 2 3 = 5.
Proof. 
  unfold sum_from_to. simpl. lra.
Qed.

Lemma sum_from_to_1 : forall (f : nat -> R) (i n : nat),
  sum_from_to' f i (S n) = sum_from_to' f i n + f ((i + S n)%nat).
Proof.
  intros f i n.
  simpl. reflexivity.
Qed.

Lemma sum_from_to_2 : forall (f : nat -> R) (i n : nat),
  sum_from_to' f i (S n) = sum_from_to' f (S i) (n) + f i.
Proof.
  intros f i n.
  induction n as [| k IH].
  - simpl. replace ((i+1)%nat) with (S i) by lia. lra.
  - rewrite sum_from_to_1. rewrite IH.
    replace (S i + S k)%nat with (S (S i + k))%nat by lia.
    rewrite sum_from_to_1. replace (i + S (S k))%nat with (S i + S k)%nat by lia.
    lra.
Qed.

Lemma sum_from_to_3 : forall (f : nat -> R) (i n : nat),
  (i < n)%nat ->
  sum_from_to' f (S i) (n - S i) = sum_from_to' f i (n - i) - f i.
Proof.
  intros f i n H1.
  induction n as [| n' IH].
  - lia.
  - assert (H2 : (i < n' \/ i = n')%nat) by lia. destruct H2 as [H2 | H2].
    -- replace ((S n' - i)%nat) with ((S (n' - i))%nat) by lia.
       rewrite sum_from_to_2 with (i := i) (n := (n' - i)%nat).
       simpl. lra.
    -- rewrite H2. replace ((S n' - S n')%nat) with 0%nat by lia.
       replace ((S n' - n')%nat) with 1%nat by lia.
       simpl. replace ((n' + 1)%nat) with ((S n')%nat) by lia. lra.
Qed.

Lemma sum_from_to_equ_1 : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_from_to f i n = sum_from_to f i (n-1) + f n.
Proof.
  intros f i n Hlt.
  unfold sum_from_to.
  destruct n.
  - inversion Hlt. 
  - replace (S n <? i)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct i.
    -- simpl. repeat rewrite Nat.sub_0_r. reflexivity.
    -- replace (S n - 1 <? S i)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
       replace (S n - S i)%nat with (S (S n - 1 - S i))%nat by lia.
       rewrite sum_from_to_1.
       replace (S i + S (S n - 1 - S i))%nat with (S n)%nat by lia.
       reflexivity.
Qed.

Lemma sum_from_to_equ_2 : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_from_to f i n = sum_from_to f (i+1) n + f i.
Proof.
  intros f i n Hlt.
  unfold sum_from_to.
  destruct (n <? i)%nat eqn:Hni.
  - (* This case should be impossible, because i < n by hypothesis. We use 'lia' to solve this contradiction. *)
    apply Nat.ltb_lt in Hni.
    lia.
  - destruct (n <? i+1)%nat eqn:Hni1.
    + (* This case is possible, it means that n = i, which contradicts i < n. *)
      apply Nat.ltb_lt in Hni1.
      lia.
    + (* Now we are in the case where i < n and n >= i+1, which is our real case of interest. *)
      assert (Hdec : (n - i)%nat = S (n - (i+1))%nat) by lia.
      rewrite Hdec. (* Rewrite the goal using the assertion we just proved. *)
      simpl.
      replace ((i + 1)%nat) with (S i) by lia.
      rewrite <- sum_from_to_1.
      rewrite <- sum_from_to_2. reflexivity.
Qed.

Lemma sum_from_to_equ_3 : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_from_to f (S i) n = sum_from_to f i n - f i.
Proof.
  intros f i n H.
  unfold sum_from_to.
  destruct (n <? S i)%nat eqn:Hni.
  - apply Nat.ltb_lt in Hni. lia.
  - destruct (n <? i)%nat eqn:Hni1.
    -- apply Nat.ltb_lt in Hni1. lia.
    -- rewrite sum_from_to_3. 2 : { lia. } reflexivity.
Qed.

Lemma sum_from_to_equ_4 : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_from_to f i (S n) = sum_from_to f i n + f (S n).
Proof.
  intros f i n H.
  unfold sum_from_to.
  destruct (n <? S i)%nat eqn:Hni.
  - apply Nat.ltb_lt in Hni. lia.
  - destruct (n <? i)%nat eqn:Hni1.
    -- apply Nat.ltb_lt in Hni1. lia.
    -- assert (H2 : (S n <? i = false)%nat). { apply Nat.ltb_ge. lia. }
       rewrite H2. replace ((S n - i)%nat) with ((S (n - i)%nat)) by lia. 
       rewrite sum_from_to_1. replace ((i + S (n - i))%nat) with ((S n)%nat) by lia.
       reflexivity.
Qed.

Lemma sum_from_to_0_0 : forall (f : nat -> R),
  sum_from_to f 0 0 = f 0%nat.
Proof.
  intros f.
  unfold sum_from_to.
  replace (0 <? 0)%nat with false by (symmetry; apply Nat.ltb_irrefl).
  simpl. reflexivity.
Qed.

Lemma sum_from_to_distributive :
  forall (f : nat -> R) (l u : nat) (x : R),
    x * (sum_from_to f l u) = sum_from_to (fun i => f i * x) l u.
Proof.
  intros f l u x.
  unfold sum_from_to.
  destruct (u <? l) eqn:H.
  - (* Case when end < start, the sum is zero. *)
    lra.
  - (* Case when start <= end, we proceed by induction on the distance from start to end. *)
    assert (Hdist : forall k, (k + l <= u)%nat -> 
            x * (sum_from_to' f l k) = sum_from_to' (fun i => f i * x) l k).
    { induction k as [|k' IHk'].
      - (* Base case *)
        simpl. intros H2. lra.
      - (* Inductive step *)
        intros Hk'.
        simpl. rewrite Rmult_plus_distr_l.
        rewrite IHk'.
        + lra.
        + lia. }
    apply Hdist.
    assert (H2 : (u >= l)%nat). { rewrite Nat.ltb_ge in H. apply H. }
    lia.
Qed.

Lemma sum_from_to_congruence: forall (f g : nat -> R) (l u : nat),
  (forall k, (l <= k <= u)%nat -> f k = g k) ->
  sum_from_to f l u = sum_from_to g l u.
Proof.
  intros f g l u H1.
  assert (H2 : (u < l)%nat \/ (u = l \/ u > l)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
  - unfold sum_from_to. rewrite <- Nat.ltb_lt in H2. rewrite H2. reflexivity.
  - induction u as [| u' IH].
  -- unfold sum_from_to. destruct l.
    --- simpl. rewrite H1.
      ---- reflexivity.
      ---- lia.
    --- simpl. reflexivity.
  -- rewrite H2. unfold sum_from_to. rewrite Nat.ltb_irrefl. replace ((l - l)%nat) with (0%nat) by lia.
     simpl. rewrite H1.
     --- reflexivity.
     --- lia.
  - induction u as [| u' IH].
    -- lia.
    -- assert (H3 : (u' = l)%nat \/ (u' > l)%nat) by lia. destruct H3 as [H3 | H3].
      --- rewrite H3. rewrite sum_from_to_equ_1. 2 : { lia. }
          rewrite sum_from_to_equ_1 with (i := l) (n := S l). 2 : { lia. }
          replace ((S l - 1)%nat) with (l%nat) by lia.
          rewrite H1. 2 : { lia. }
          unfold sum_from_to. rewrite Nat.ltb_irrefl. replace ((l - l)%nat) with (0%nat) by lia.
          simpl. rewrite H1.
          ---- reflexivity.
          ---- lia.
      --- rewrite sum_from_to_equ_1. 2 : { lia. }
          rewrite sum_from_to_equ_1 with (i := l) (n := S u'). 2 : { lia. }
          replace ((S u' - 1)%nat) with (u'%nat) by lia.
          rewrite IH.
          ---- rewrite H1.
               ----- reflexivity.
               ----- lia.
          ---- intros k H4. apply H1. lia.
          ---- lia.
Qed.
    
Theorem sums_equivalent : forall (l u : nat) (x y : R) (f1 f2 : nat -> R),
  (forall i : nat, (l <= i <= u )%nat -> f1 i = f2 i) ->
    sum_from_to f1 l u = sum_from_to f2 l u.
Proof.
  intros l u x y f1 f2 H1.
  apply sum_from_to_congruence. apply H1.
Qed.

Lemma sum_reindex : forall (f : nat -> R) (l u s : nat),
  (s <= l < u)%nat ->
  sum_from_to f l u = sum_from_to (fun i => f (i + s)%nat) (l - s) (u - s).
Proof.
  intros f l u s H.
  assert ((s < l)%nat \/ (s = l)%nat) by lia. destruct H0 as [H0 | H0].
  induction l as [| l' IH].
  - simpl. replace ((s)%nat) with (0%nat) by lia. rewrite Nat.sub_0_r.
    apply sum_from_to_congruence. intros k H1. replace ((k + 0)%nat) with (k%nat) by lia. reflexivity.
  - rewrite sum_from_to_equ_2. 2 : { lia. }
    replace ((S l' - s)%nat) with (S (l' - s)%nat) by lia.
    rewrite sum_from_to_equ_3. 2 : { lia. }
    assert (H2 : (s < l')%nat \/ (s = l')%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite <- IH. 2 : { lia. } replace ((l' - s + s)%nat) with (l'%nat) by lia.
       simpl. rewrite sum_from_to_equ_3. 2 : { lia. }
       replace ((l' + 1)%nat) with (S l') by lia. 
       rewrite sum_from_to_equ_3. 2 : { lia. } lra. lia.
    -- rewrite H2. simpl. replace ((l' - l')%nat) with (0%nat) by lia. simpl.
       rewrite sum_from_to_equ_3. 2 : { lia. }
       replace ((l' + 1)%nat) with (S l') by lia. 
       rewrite sum_from_to_equ_3. 2 : { lia. }
       induction u. 
       --- lia.
       --- assert (H3 : (u = S l')%nat \/ (u > S l')%nat) by lia. rewrite sum_from_to_equ_4. 2 : { lia. }
            replace ((S u - l')%nat) with (S (u - l')%nat) by lia.
            rewrite sum_from_to_equ_4. 2 : { lia. }
            replace ((S (S u) - S (S u))%nat) with (0%nat) by lia.
            simpl. replace ((u - l' + l')%nat) with (u%nat) by lia.
            ------ replace (sum_from_to (fun i : nat => f (i + l')%nat) 0 (u - l') + f (S u) - f l') with 
                          (sum_from_to (fun i : nat => f (i + l')%nat) 0 (u - l') - f l' + f (S u)) by lra.
            destruct H3 as [H3 | H3].
            ------- rewrite H3. rewrite sum_from_to_equ_2. 2 : { lia. }
                    replace ((S l' - l')%nat) with 1%nat by lia.
                    assert (H4 : sum_from_to f (l' + 1) (S l') = f (l' + 1)%nat).
                    { unfold sum_from_to. replace ((S l' <? l' + 1)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
                      replace ((S l' - (l' + 1))%nat) with 0%nat by lia. simpl. reflexivity. }
                    assert (H5 : sum_from_to (fun i : nat => f (i + l')%nat) 0 1 = f (0 + l')%nat + f (S l')).
                    { unfold sum_from_to. simpl. lra. }
                    rewrite H4. rewrite H5. simpl. replace ((l' + 1)%nat) with (S l') by lia. lra.
            -------
            rewrite <- IHu. lra. 2 : { lia. } lia.
  - rewrite H0. replace ((l - l)%nat) with (0%nat) by lia.
    induction u.
    -- simpl. unfold sum_from_to. replace ((0 <? 0)%nat) with false by (symmetry; apply Nat.ltb_irrefl).
       simpl. assert (H1 : (0 <? l)%nat = false). { lia. } rewrite H1. reflexivity.
    -- rewrite sum_from_to_equ_1. 2 : { lia. }
       replace ((S u - 1)%nat) with (u%nat) by lia. assert (H2 : (l = u)%nat \/ (l < u)%nat) by lia.
       destruct H2 as [H2 | H2].
       --- rewrite H2. replace ((S u - u)%nat) with 1%nat by lia.
          assert (H3 : sum_from_to f u u = f u).
          { unfold sum_from_to. rewrite Nat.ltb_irrefl. replace ((u - u)%nat) with 0%nat by lia. simpl. reflexivity. }
          assert (H4 : sum_from_to (fun i : nat => f (i + u)%nat) 0 1 = f (u) + f (S u)).
          { unfold sum_from_to. simpl. reflexivity. }
          rewrite H3. rewrite H4. simpl. lra.
       --- rewrite IHu. 2 : { lia. }
            replace ((S u - l)%nat) with (S (u - l)%nat) by lia.
            rewrite sum_from_to_equ_4. 2 : { lia. }
            replace ((S (u - l) + l)%nat) with ((S u)%nat) by lia. lra.
Qed.

Theorem pow_equ : forall (r: R) (a : nat),
  (a > 0)%nat -> r ^ a = r * r ^ (a - 1).
Proof.
  intros r a H1. destruct a.
  - lia.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma lemma_1_1_v : forall (x y : R) (n : nat),
  (n >= 1)%nat ->
  x ^ n - y ^ n = (x - y) * sum_from_to (fun i => x ^ i * y ^ (n - i - 1)) 0 (n-1).
Proof.
  intros x y n H1.
  assert (H2 : (n = 1 \/ n = 2 \/ n = 3 \/ n >= 4)%nat) by lia. destruct H2 as [H2 | [H2 | [H2 | H2]]].
  - rewrite H2. compute. lra.
  - rewrite H2. compute. lra.
  - rewrite H2. compute. lra.
  - rewrite Rmult_minus_distr_r. rewrite sum_from_to_equ_1 at 1. 2: lia.
    replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
    replace ((n - (n - 1) - 1)%nat) with 0%nat by lia.
    replace (y ^ 0) with 1 by lra. rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_l. replace (x * x ^ (n - 1)) with (x ^ n). 
      2 : { destruct n. simpl. lia. simpl. rewrite Nat.sub_0_r. reflexivity. }
    assert (H3 : x * sum_from_to (fun i : nat => x ^ i * y ^ (n - i - 1)) 0 (n - 2)
                = sum_from_to (fun i : nat => x ^ (i + 1) * y ^ (n - 1 - i)) 0 (n - 2)).
      {
        rewrite sum_from_to_distributive. 
        set (f1 := fun i : nat => x ^ i * y ^ (n - i - 1) * x).
        set (f2 := fun i : nat => x ^ (i + 1) * y ^ (n - 1 - i)).
        assert (forall i : nat, f1 i = f2 i).
        { intro i. unfold f1. unfold f2. replace (i + 1)%nat with (S i) by lia.
          replace (n - 1 - i)%nat with (n - i - 1)%nat by lia.
          replace (x ^ i * y ^ (n - i - 1) * x) with (x ^ i * x * y ^ (n - i - 1)) by lra.
          simpl. lra.
        }
        apply functional_extensionality in H. rewrite H. reflexivity.
      }
      rewrite H3. rewrite sum_from_to_equ_2 with (i := 0%nat) (n := (n-1)%nat). 2: lia.
      replace (x ^ 0) with 1 by lra. rewrite Rmult_1_l.
      replace ((n - 0 - 1)%nat) with (n - 1)%nat by lia.
      rewrite Nat.add_0_l.
      assert (H4 : y * (sum_from_to (fun i : nat => x ^ i * y ^ (n - i - 1)) 1 (n - 1) + y ^ (n - 1))
                = sum_from_to (fun i : nat => x ^ i * y ^ (n - i)) 1 (n - 1) + y ^ (n)).
        {
          rewrite Rmult_plus_distr_l. rewrite <- pow_equ. 2 : { lia. }
          rewrite sum_from_to_distributive.
          set (f1 := fun i : nat => x ^ i * y ^ (n - i - 1) * y).
          set (f2 := fun i : nat => x ^ i * y ^ (n - i)).
          rewrite sums_equivalent with (f1 := f1) (f2 := f2). reflexivity. auto. auto.
          intros i H4. destruct i.
          - lia.
          - unfold f1. unfold f2. simpl. assert (H5 : (n - S i = 0)%nat \/ (n - S i > 0)%nat) by lia.
            destruct H5 as [H5 | H5].
            -- lia.
            -- rewrite pow_equ with (r := y) (a := (n - S i)%nat). 2 : { lia. } lra.
        }
      rewrite H4. rewrite sum_reindex with (s := 1%nat) (l := 1%nat). 2 : { lia. }
      replace ((1 - 1)%nat) with 0%nat by lia. replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
      assert (H5 : sum_from_to (fun i : nat => x ^ (i+1) * y ^ (n - 1 - i)) 0 (n - 2) = 
                   sum_from_to (fun i : nat => x ^ (i+1) * y ^ (n - (i+1))) 0 (n - 2)).
        { apply sum_from_to_congruence. intros i H5. replace ((n - 1 - i)%nat) with (n - (i+1))%nat by lia. reflexivity. }
      rewrite H5. lra.
Qed.

Example example_1_1_1 : forall (x y : R),
  x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2).
Proof. 
  intros x y. rewrite lemma_1_1_v with (n := 3%nat). compute. lra. lia.
Qed.


Lemma lemma_1_1_vi : forall (x y : R) (n : nat),
  (n >= 1)%nat ->
  x ^ 3 + y ^ 3 = (x + y) * sum_from_to (fun i => (-1) ^ i * x ^ (n - i - 1) * y ^ i) 0 (2).
Proof.
  intros x y n H1.
  induction n as [| n' IH].
  - lia.
  - rewrite sum_from_to_equ_1. rewrite sum_from_to_equ_1.
    -- replace ((2 - 1 - 1)%nat) with (0%nat) by lia. rewrite sum_from_to_0_0. simpl.
       repeat rewrite Rmult_1_r. rewrite Rmult_1_l. repeat rewrite Nat.sub_0_r. 
       