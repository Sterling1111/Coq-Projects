Require Import Reals Lra Lia ZArith FunctionalExtensionality List Classical.
Import ListNotations.
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
  x ^ 2 - y ^ 2 = (x - y) * (x + y).
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
  x ^ 2 = y ^ 2 -> x = y \/ x = -y.
Proof.
  intros x y H.
  assert (H1 : x ^ 2 - y ^ 2 = 0) by lra.
  rewrite lemma_1_1_ii in H1. apply Rmult_integral in H1.
  destruct H1 as [H1 | H1].
  - left. apply Rminus_diag_uniq in H1. apply H1.
  - right. rewrite Rplus_comm in H1. apply Rplus_opp_r_uniq in H1. apply H1.
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

Lemma sum_f_R0_f_Sn : forall f n,
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  destruct n; simpl; lra.
Qed.

Lemma sum_f_R0_fSx_n : forall n f,
  sum_f_R0 (fun x => f (S x)) n = sum_f_R0 f (S n) - f 0%nat.
Proof.
  intros. induction n.
  - simpl. lra.
  - simpl. rewrite IHn. rewrite sum_f_R0_f_Sn. lra.
Qed.

Lemma sum_f_R0_fSxplusa_n : forall n a f,
  sum_f_R0 (fun x => f (S (x + a))%nat) n = sum_f_R0 (fun x => f (x + a)%nat) (S n) - f a.
Proof.
  intros n a f.
  induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. rewrite sum_f_R0_f_Sn. simpl. lra.
Qed.

Lemma sum_f_Pn: forall f i n,
  (i < n)%nat -> sum_f i n f = sum_f i (Nat.pred n) f + f n.
Proof.
  intros. replace (Nat.pred n) with (n-1)%nat by lia. induction n as [| k IH].
  - lia.
  - replace ((S k - 1)%nat) with (k%nat) by lia.
    assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite IH. 2 : { lia. }
       unfold sum_f. replace ((S k - i)%nat) with ((S (k - i))%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((k - i)%nat) with (S (k - 1 - i)%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((S (k - 1 - i) + i))%nat with (k%nat) by lia.
       replace ((S (S (k - 1 - i)) + i))%nat with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. unfold sum_f. replace ((S k - k)%nat) with 1%nat by lia.
       replace ((k - k)%nat) with 0%nat by lia. simpl. lra.
Qed.

Lemma sum_f_Si : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f i n f = sum_f (S i) n f + f i.
Proof.
  intros f i n H1.
  replace (S i) with (i+1)%nat by lia.
  unfold sum_f. replace (n - i)%nat with (S (n - i - 1)) by lia.
  rewrite sum_f_R0_f_Sn. replace (S (n - i - 1) + i)%nat with n%nat by lia.
  replace ((fun x : nat => f (x + (i + 1))%nat)) with (fun x : nat => f (S x + i)%nat).
  rewrite sum_f_R0_fSxplusa_n with (a := i%nat). simpl. 
  replace (S (n - (i+1) + i)%nat) with n%nat by lia.
  replace (n - (i+1))%nat with (n - i - 1)%nat by lia. lra.
  apply functional_extensionality. intros x. replace (x + (i + 1))%nat with (S x + i)%nat by lia. lra.
Qed.

Lemma sum_f_i_Sn_f : forall f i n,
  (i < n)%nat -> sum_f i (S n) f = sum_f i n f + f (S n).
Proof.
  intros f i n H.
  induction n as [| k IH].
  - replace i%nat with 0%nat by lia. unfold sum_f. simpl. lra.
  - assert (H2 : (i = k \/ i < k)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite H2. unfold sum_f. replace ((S k - k)%nat) with 1%nat by lia.
       replace (S (S k) - k)%nat with 2%nat by lia. simpl. lra.
    -- rewrite IH.
       --- unfold sum_f. replace ((S (S k) - i)%nat) with (S (S k - i))%nat by lia.
           rewrite sum_f_R0_f_Sn. replace (S k - i)%nat with (S (k - i))%nat by lia.
           rewrite sum_f_R0_f_Sn. replace ((S (k - i) + i)%nat) with (S k)%nat by lia.
           replace (S (S (k - i)) + i)%nat with (S (S k))%nat by lia. reflexivity.
       --- lia.
Qed.

Lemma sum_f_Si_n_f : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f (S i) n f = sum_f i n f - f i.
Proof.
  intros f i n H.
  unfold sum_f.
  induction n as [| k IH].
  - lia.
  - assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- replace ((S k - i)%nat) with (S(k - i)%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((S (k - i) + i)%nat) with ((S k)%nat) by lia.
       replace (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) + f (S k) - f i)
       with (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) - f i + f (S k)) by lra. rewrite <- IH.
       2 : { lia. } replace ((S k - S i)%nat) with (S (k - S i)%nat) by lia. rewrite sum_f_R0_f_Sn.
       replace ((S (k - S i) + S i)%nat) with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. replace ((S k - k)%nat) with 1%nat by lia. replace ((S k - S k)%nat) with 0%nat by lia.
       simpl. lra.
Qed.


Lemma sum_f_0_0 : forall f,
  sum_f 0 0 f = f 0%nat.
Proof.
  intros. unfold sum_f. simpl. lra.
Qed.

Lemma sum_f_n_n : forall f n,
  sum_f n n f = f n.
Proof.
  intros. unfold sum_f. rewrite Nat.sub_diag. simpl. lra.
Qed.

Lemma sum_f_Sn_n : forall n1 n2 f,
  (n1 > n2)%nat -> sum_f n1 n2 f = f n1%nat.
Proof.
  intros. unfold sum_f. replace (n2 - n1)%nat with 0%nat by lia.
  unfold sum_f_R0. simpl. reflexivity.
Qed.

Lemma r_mult_sum_f_i_n_f :
  forall f i n r,
    r * (sum_f i n f) = sum_f i n (fun i => f i * r).
Proof.
  intros. unfold sum_f.
  set (k := (n - i)%nat).
  induction k as [| k' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. lra. 
Qed.

Lemma sum_f_sum :
  forall f g i n, 
    sum_f i n f + sum_f i n g = sum_f i n (fun x : nat => f x + g x).
Proof.
  intros. induction n as [| k IH].
  - unfold sum_f. simpl. reflexivity.
  - assert (H: (i < k)%nat \/ (i = k)%nat \/ (i > k)%nat) by lia. destruct H as [H | [H | H]].
    -- repeat rewrite sum_f_i_Sn_f. 2 : { lia. } 2 : { lia. } 2 : { lia. }
       replace (sum_f i k f + f (S k) + (sum_f i k g + g (S k))) with (sum_f i k f + sum_f i k g + f (S k) + g (S k)) by lra.
       rewrite IH. lra.
    -- rewrite H. unfold sum_f. replace (S k - k)%nat with 1%nat by lia. simpl. lra.
    -- assert (H2 : (i > S k)%nat \/ (i = S k)%nat) by lia. destruct H2 as [H2 | H2].
       --- repeat rewrite sum_f_Sn_n. 2 : { lia. } 2 : { lia. } 2 : { lia. } lra.
       --- rewrite <- H2. repeat rewrite sum_f_n_n. lra.
Qed.
        

Lemma sum_f_congruence: forall (f1 f2 : nat -> R) (i n : nat),
(i <= n)%nat ->
(forall k, (i <= k <= n)%nat -> f1 k = f2 k) ->
sum_f i n f1 = sum_f i n f2.
Proof.
  intros f1 f2 i n H1 H2.
  unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. rewrite H2.
       2 : { lia. } reflexivity.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       rewrite IH. 2 : { lia. } rewrite H2. 2 : { lia. } reflexivity. intros k H4. apply H2. lia.
Qed.

Theorem sum_f_equiv : forall (i n : nat) (f1 f2 : nat -> R),
  (i <= n)%nat ->
  (forall k : nat, (i <= k <= n )%nat -> f1 k = f2 k) ->
    sum_f i n f1 = sum_f i n f2.
Proof.
  intros i n f1 f2 H1 H2.
  apply sum_f_congruence. apply H1. apply H2.
Qed.

Theorem sum_f_reindex : forall (f : nat -> R) (i n s : nat),
  (s <= i <= n)%nat ->
  sum_f i n f = sum_f (i - s) (n - s) (fun x => f (x + s)%nat).
Proof.
  intros f i n s H.
  induction i as [| i' IH].
  - simpl. replace ((s)%nat) with (0%nat) by lia. rewrite Nat.sub_0_r.
    apply sum_f_congruence. lia. intros k. replace ((k + 0)%nat) with (k%nat) by lia. reflexivity.
  - assert (H2 : (S i' = n)%nat \/ (S i' < n)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite H2. repeat rewrite sum_f_n_n. replace ((n - s + s)%nat) with ((n)%nat) by lia. reflexivity.
    -- rewrite sum_f_Si_n_f. 2 : { lia. }
       assert (H3 : (s <= i')%nat \/ (s = S i')) by lia. destruct H3 as [H3 | H3].
       --- rewrite IH. 2 : { lia. }
            replace ((S i' - s)%nat) with (S (i' - s)%nat) by lia.
            rewrite sum_f_Si_n_f. 2 : { lia. }
            replace ((i' - s + s)%nat) with ((i')%nat) by lia. lra.
       --- rewrite <- H3. replace ((S i' - S i')%nat) with (0%nat) by lia. simpl.
           unfold sum_f. replace ((n - s - (s - s))%nat) with ((n - s)%nat) by lia.
           replace ((n - i')%nat) with (S (n - s)%nat) by lia.
           rewrite sum_f_R0_f_Sn. simpl. replace ((S (n - s + i')%nat)) with n%nat by lia.
           set (f2 := fun x : nat => f (S (x + i'))%nat).
           replace (fun x : nat => f (x + (s - s) + s)%nat) with (fun x : nat => f (S x + i')%nat).
           2 : { apply functional_extensionality. intros x. replace (x + (s - s) + s)%nat with (x + S i')%nat by lia.
           replace (S x + i')%nat with (x + S i')%nat by lia. reflexivity. }
           replace (fun x : nat => f (S x + i')%nat) with f2. 2 : { apply functional_extensionality. unfold f2. simpl. reflexivity. }
           unfold f2. rewrite sum_f_R0_fSxplusa_n. simpl. replace (S (n - s + i')%nat) with n%nat by lia. lra.
Qed.

Theorem sum_f_reindex' : forall (f : nat -> R) (i n s : nat),
  sum_f i n f = sum_f (i + s) (n + s) (fun x => f (x - s)%nat).
Proof.
  intros f i n s.
  induction i as [| i' IH].
  - simpl. unfold sum_f. replace (fun x : nat => f (x + s - s)%nat) with (fun x : nat => (f x%nat)).
    2 : { apply functional_extensionality. intros x. replace (x + s - s)%nat with x%nat by lia. reflexivity. }
    replace (n + s - s)%nat with n%nat by lia. 
    replace (fun x : nat => f (x + 0)%nat) with (fun x : nat => (f x)).
    2 : { apply functional_extensionality. intro x. rewrite Nat.add_0_r. reflexivity. }
    rewrite Nat.sub_0_r. reflexivity.
  - replace (S i' + s)%nat with (S (i' + s)) by lia.
    assert (H2 : (i' < n)%nat \/ (i' = n)%nat \/ (i' > n)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
    -- rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_Si_n_f. 2 : { lia. } rewrite IH.
       replace (i' + s - s)%nat with (i')%nat by lia. reflexivity.
    -- rewrite H2. rewrite sum_f_Sn_n by lia. rewrite sum_f_Sn_n by lia. replace ((S (n + s) - s)%nat) with (S n) by lia.
       reflexivity.
    -- repeat rewrite sum_f_Sn_n by lia. replace (S (i' + s) - s)%nat with (S i') by lia.
       reflexivity.
Qed.

Theorem pow_equ : forall (r: R) (a : nat),
  (a > 0)%nat -> r ^ a = r * r ^ (a - 1).
Proof.
  intros r a H1. destruct a.
  - lia.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma pow_equ' : forall r a,
  r ^ (a) * r = r ^ (a + 1).
Proof.
    intros r a. induction a as [| k IH].
    - simpl. lra.
    - simpl. rewrite <- IH. lra.
Qed. 

Lemma lemma_1_1_v : forall (x y : R) (n : nat),
  (n >= 1)%nat ->
  x ^ n - y ^ n = (x - y) * sum_f 0 (n-1) (fun i => x ^ i * y ^ (n - i - 1)).
Proof.
  intros x y n H1.
  assert (H2 : (n = 1 \/ (n >= 2))%nat) by lia. destruct H2 as [H2 | H2].
  - rewrite H2. compute. lra.
  - rewrite Rmult_minus_distr_r. rewrite sum_f_Pn at 1. 2: lia.
    replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
    replace ((n - (n - 1) - 1)%nat) with 0%nat by lia.
    replace (y ^ 0) with 1 by lra. rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_l. replace (x * x ^ (n - 1)) with (x ^ n). 
      2 : { destruct n. simpl. lia. simpl. rewrite Nat.sub_0_r. reflexivity. }
    assert (H3 : x * sum_f 0 (n - 2) (fun i : nat => x ^ i * y ^ (n - i - 1))
                = sum_f 0 (n - 2) (fun i : nat => x ^ (i + 1) * y ^ (n - 1 - i))).
      {
        rewrite r_mult_sum_f_i_n_f.
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
      replace (Nat.pred (n - 1)) with (n - 2)%nat by lia.
      rewrite H3. rewrite sum_f_Si with (i := 0%nat) (n := (n-1)%nat). 2: lia.
      replace (x ^ 0) with 1 by lra. rewrite Rmult_1_l.
      replace ((n - 0 - 1)%nat) with (n - 1)%nat by lia.
      assert (H4 : y * (sum_f 1 (n - 1) (fun i : nat => x ^ i * y ^ (n - i - 1)) + y ^ (n - 1))
                = sum_f 1 (n - 1) (fun i : nat => x ^ i * y ^ (n - i)) + y ^ (n)).
        {
          rewrite Rmult_plus_distr_l. rewrite <- pow_equ. 2 : { lia. }
          rewrite r_mult_sum_f_i_n_f.
          set (f1 := fun i : nat => x ^ i * y ^ (n - i - 1) * y).
          set (f2 := fun i : nat => x ^ i * y ^ (n - i)).
          rewrite sum_f_equiv with (f1 := f1) (f2 := f2). reflexivity. auto. auto. lia.
          intros i. destruct i.
          - lia.
          - unfold f1. unfold f2. simpl. assert (H5 : (n - S i = 0)%nat \/ (n - S i > 0)%nat) by lia.
            destruct H5 as [H5 | H5].
            -- lia.
            -- rewrite pow_equ with (r := y) (a := (n - S i)%nat). 2 : { lia. } lra.
        }
      rewrite H4. rewrite sum_f_reindex with (s := 1%nat) (i := 1%nat). 2 : { lia. }
      replace ((1 - 1)%nat) with 0%nat by lia. replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
      assert (H5 : sum_f 0 (n - 2) (fun i : nat => x ^ (i+1) * y ^ (n - 1 - i)) = 
                   sum_f 0 (n - 2) (fun i : nat => x ^ (i+1) * y ^ (n - (i+1)))).
        { apply sum_f_congruence. lia. intros i H5. replace ((n - 1 - i)%nat) with (n - (i+1))%nat by lia. reflexivity. }
      rewrite H5. lra.
Qed.

Example example_1_1_1 : forall (x y : R),
  x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2).
Proof. 
  intros x y. rewrite lemma_1_1_v with (n := 3%nat). compute. lra. lia.
Qed.

Lemma lemma_1_1_vi : forall (x y : R),
  x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2).
Proof.
  intros x y. assert (H1 : x ^ 3 + y ^ 3 = x ^ 3 - ((- y) ^ 3)) by lra.
  rewrite H1. rewrite lemma_1_1_iv with (x := x) (y := -y). 
  replace (x -- y) with (x + y) by lra. replace (x * - y) with (- x * y) by lra.
  replace ((-y) ^ 2) with (y ^ 2) by lra. lra.
Qed.

Lemma lemma_1_2 : forall x y : R,
  x = y -> 1 = 2.
Proof.
  intros x y H1. pose proof H1 as H2.
  apply Rmult_eq_compat_l with (r := x) in H1.
  apply Rminus_eq_compat_r with (r := y^2) in H1.
  replace (x * x) with (x ^ 2) in H1 by lra.
  rewrite lemma_1_1_ii in H1. replace (y^2) with (y * y) in H1 by lra.
  rewrite <- Rmult_minus_distr_r in H1.
  apply Rmult_eq_reg_l in H1.
  - rewrite H2 in H1. replace (y + y) with (2 * y) in H1 by lra. 
    apply Rmult_eq_compat_r with (r := 1 / y) in H1. rewrite Rmult_assoc in H1.
    unfold Rdiv in H1. rewrite Rmult_1_l in H1. rewrite Rmult_comm with (r1 := y) in H1.
    assert (H3 : y <> 0 \/ y = 0) by lra. destruct H3 as [H3 | H3].
    -- rewrite Rinv_l in H1.
       --- rewrite Rmult_1_r in H1. rewrite H1. reflexivity.
       --- apply H3.
    -- (*we fail here because y is 0 so cant apply Rinv_l*) admit.
  - apply Rminus_diag_eq in H2. (* we fail here again because x - y = 0*) 
Abort.

(*we dont need b <> 0 in this proof because in coq r / 0 = 0 so it hold true anyway*)
Lemma lemma_1_3_i : forall a b c : R,
  b <> 0 /\ c <> 0 -> a / b = (a * c) / (b * c).
Proof.
  intros a b c [H1 H2].
  unfold Rdiv.
  rewrite Rinv_mult. rewrite Rmult_assoc. rewrite Rmult_comm with (r1 := c).
  rewrite Rmult_assoc with (r3 := c). rewrite Rinv_l. 2 : { apply H2. }
  rewrite Rmult_1_r. reflexivity.
Qed.

Lemma lemma_1_3_ii : forall a b c d : R,
  b <> 0 /\ d <> 0 -> a / b + c / d = (a * d + b * c) / (b * d).
Proof.
  intros a b c d [H1 H2].
  unfold Rdiv. rewrite Rinv_mult. rewrite <- Rmult_assoc. 
  apply Rmult_eq_reg_r with (r := d). 2 : { apply H2. }
  rewrite Rmult_plus_distr_r. rewrite Rmult_assoc with (r1 := c).
  rewrite Rinv_l. 2 : { apply H2. } rewrite Rmult_1_r. 
  rewrite Rmult_plus_distr_r. rewrite Rmult_comm with (r1 := b).
  rewrite Rmult_assoc with (r1 := c). rewrite Rinv_r. 2 : { apply H1. }
  rewrite Rmult_1_r. rewrite Rmult_assoc with (r2 := /d). rewrite Rinv_l.
  2 : { apply H2. } rewrite Rmult_1_r. rewrite Rmult_assoc. rewrite Rmult_comm with (r2 := d).
  rewrite Rmult_assoc. reflexivity.
Qed.

Definition Zpow (b : R) (e : Z) : R :=
  if Z.ltb e 0 then 1 / (b ^ Z.to_nat (Z.abs e)) else b ^ Z.to_nat e.

Lemma lemma_1_3_iii : forall a b : R,
  a > 0 /\ b > 0 -> Rpower (a * b) (-1) = Rpower a (-1) * Rpower b (-1).
Proof.
  intros a b [H1 H2].
  repeat rewrite Rpower_Ropp with (y := 1). repeat rewrite Rpower_1.
  2 : {  apply H2. } 2 : { apply H1. } 2 : { apply Rmult_lt_0_compat; assumption. }
  apply Rinv_mult.
Qed.

Lemma lemma_1_3_iii' : forall a b : R, 
  a <> 0 /\ b <> 0 -> Zpow (a * b) (-1)%Z = Zpow a (-1)%Z * Zpow b (-1)%Z.
Proof.
  intros a b [H1 H2].
  - unfold Zpow. simpl. field; lra.
Qed.

Lemma lemma_1_3_iv : forall a b c d : R,
  b <> 0 /\ d <> 0 -> (a / b) * (c / d) = (a * c) / (d * b).
Proof.
  intros a b c d [H1 H2].
  unfold Rdiv. rewrite Rinv_mult.
  rewrite Rmult_assoc. rewrite Rmult_assoc. rewrite Rmult_comm with (r2 := /d * /b).
  rewrite Rmult_comm with (r1 := /d). rewrite Rmult_assoc with (r1 := /b).
  rewrite Rmult_comm with (r1 := /d). reflexivity.
Qed.

Lemma lemma_1_3_v : forall a b c d : R,
  b <> 0 /\ c <> 0 /\ d <> 0 -> (a / b) / (c / d) = (a * d) / (b * c).
Proof.
  intros a b c d [H1 [H3 H4]].
  unfold Rdiv. repeat rewrite Rinv_mult. rewrite Rinv_inv. lra. (*more tedius assoc + commutativity who cares*) 
Qed.

Lemma lemma_1_3_vi : forall a b c d, 
  b <> 0 /\ d <> 0 -> a / b = c / d <-> a * d = b * c.
Proof.
  intros a b c d [H1 H2].
  split.
  - intros H3. apply Rmult_eq_compat_r with (r := b) in H3.
    unfold Rdiv in H3. rewrite Rmult_assoc in H3.
    rewrite Rinv_l in H3. 2 : { apply H1. } rewrite Rmult_1_r in H3.
    rewrite -> H3. replace (c * / d * b * d) with (/d * d * b * c) by lra.
    rewrite Rinv_l. 2 : { apply H2. } rewrite Rmult_1_l. reflexivity.
  - intros H3. apply Rmult_eq_compat_r with (r := /d) in H3.
    unfold Rdiv in H3. rewrite Rmult_assoc in H3. rewrite Rinv_r in H3. 2 : { apply H2. }
    rewrite Rmult_1_r in H3. rewrite H3. unfold Rdiv.
    replace (b * c * /d * /b) with (c * /d *( b * /b)) by lra. rewrite Rinv_r.
    2 : {apply H1. } rewrite Rmult_1_r. reflexivity.
Qed.

Lemma lemma_1_4_i : forall x : R,
  x < -1 <-> 4 - x < 3 - 2 * x.
Proof.
  intro x. split.
  - intro H. apply Rplus_lt_compat_r with (r := - 2 * x) in H.
    apply Rplus_lt_compat_r with (r := 4) in H. 
    replace (x + -2 * x + 4) with (4 - x) in H by lra.
    replace (-1 + -2 * x + 4) with (3 - 2 * x) in H by lra.
    apply H.
  - intro H. apply Rplus_lt_compat_r with (r := 2 * x) in H.
    apply Rplus_lt_compat_r with (r := -4) in H.
    replace (4 - x + 2 * x + -4) with (x) in H by lra.
    replace (3 - 2 * x + 2 * x + -4) with (-1) in H by lra.
    apply H.
Qed.

Lemma lemma_1_4_ii : forall x : R,
  5 - x^2 < 8.
Proof.
  intro x. apply Rplus_lt_reg_l with (r := -5).
  replace (-5 + (5 - x ^ 2)) with (-x^2) by lra. replace (-5+8) with (--3) by lra.
  apply Ropp_lt_gt_contravar. simpl. rewrite Rmult_1_r. rewrite <- Rsqr_def. 
  assert (0 <= Rsqr x) by apply Rle_0_sqr. lra.
Qed.


Lemma lemma_1_4_iii : forall x : R,
  x > sqrt 7 \/ x < - sqrt 7 <-> 5 - x^2 < - 2.
Proof.
  intros. split. 
  - intros [H1 | H2].
    -- assert (H2 : 0 <= sqrt 7) by (apply sqrt_positivity; lra). assert (H3 : x > 0) by lra.
       assert (H4 : x * x > sqrt 7 * sqrt 7). nra.
       rewrite sqrt_sqrt in H4. assert (H5: x * x > 7) by apply H4. lra. lra.
    -- assert (H3 : 0 <= sqrt 7) by (apply sqrt_positivity; lra). assert (H4 : -x > 0) by lra.
       assert (H5 : (-x) * (-x) > sqrt 7 * sqrt 7) by nra.
       rewrite sqrt_sqrt in H5. replace (-x * -x) with (x * x) in H5 by lra. 
       assert (H6 : x * x > 7) by apply H5. lra. lra.
  - intro H1. assert (H2 : x^2 > 7) by nra. rewrite <- sqrt_sqrt in H2. 2 : { lra. } nra.
Qed.

Lemma lemma_1_4_iv : forall x : R,
  x < 1 \/ x > 3 <-> (x - 1) * (x - 3) > 0.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- assert (H3 : x - 1 < 0) by lra. assert (H4 : x - 3 < 0) by lra. nra.
    -- assert (H3 : x - 1 > 0) by lra. assert (H4 : x - 3 > 0) by lra. nra.
  - intro H. nra.
Qed.

Lemma lemma_1_4_v : forall x : R,
  x^2 - 2 * x + 2 > 0.
Proof.
  intros x. nra.
Qed.

Lemma two_less_sqrt_five : 2 < sqrt 5.
Proof.
  assert (sqrt (2 * 2) < sqrt (5)). { apply sqrt_lt_1. lra. lra. lra. }
  rewrite sqrt_square in H. 2 : { lra. } apply H.
Qed.

Lemma lemma_1_4_vi : forall x : R,
  x > (-1 + sqrt 5) / 2 \/ x < (-1 - sqrt 5) / 2 <-> x^2 + x + 1 > 2.
Proof.
  intros x. pose proof two_less_sqrt_five. split.
  - intros [H1 | H2].
    -- assert (H2 : 2 * x + 1 > (sqrt 5)) by lra.
       rewrite <- pow2_sqrt with (x := 2 * x + 1) in H2.
       --- simpl in H2. rewrite Rmult_1_r in H2. rewrite <- sqrt_mult in H2.
        ---- apply Rgt_lt in H2. apply sqrt_lt_0_alt in H2. lra.
        ---- lra.
        ---- lra.
       --- lra.
    -- assert (H3 : -2 * x - 1 > sqrt 5) by lra.
       rewrite <- pow2_sqrt with (x := -2 * x - 1) in H3.
       --- simpl in H3. rewrite Rmult_1_r in H3. rewrite <- sqrt_mult in H3.
        ---- apply Rgt_lt in H3. apply sqrt_lt_0_alt in H3. lra.
        ---- lra.
        ---- lra.
       --- lra.
  - intros H1. assert (H2 : x^2 + x - 1 > 0) by nra.
    replace (x^2 + x - 1) with ((x - (-1 + sqrt 5) / 2) * (x - (-1 - sqrt 5) / 2)) in H2. 2 :
       {
         set (r1 := (-1 + sqrt 5) / 2). set (r2 := (-1 - sqrt 5) / 2). replace ((x - r1) * (x - r2)) with (x^2 - x * (r2 + r1) + r1 * r2) by lra.
         assert (H3 : r1 + r2 = -1) by (unfold r1, r2; lra).
         assert (H4 : r1 * r2 = -1).
         {
            unfold r1, r2. apply Rmult_eq_reg_r with (r := 4). 2 : { lra. }
            replace (((-1 + sqrt 5) / 2) * ((-1 - sqrt 5) / 2) * 4) with ((-1 - sqrt 5) * (-1 + sqrt 5)) by nra.
            replace (-1 * 4) with (-4) by lra. replace ((-1 - sqrt 5) * (-1 + sqrt 5)) with (1^2 - (sqrt 5)^2) by lra.
            rewrite pow2_sqrt. lra. lra.
         } nra.
       } nra. 
Qed.

Lemma lemma_1_4_vii : forall x : R,
  x < -2 \/ x > 3 <-> x^2 - x + 10 > 16.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- apply Rplus_gt_reg_r with (r := -16). replace (x^2 - x + 10 + -16) with (x^2 - x - 6) by lra.
       replace (16 + -16) with 0 by lra. replace (x^2 - x - 6) with ((x - 3) * (x + 2)) by lra.
       assert (H3 : x - 3 < 0) by lra. assert (H4 : x + 2 < 0) by lra. nra.
    -- apply Rplus_gt_reg_r with (r := -16). replace (x^2 - x + 10 + -16) with (x^2 - x - 6) by lra.
       replace (16 + -16) with 0 by lra. replace (x^2 - x - 6) with ((x - 3) * (x + 2)) by lra.
       assert (H3 : x - 3 > 0) by lra. assert (H4 : x + 2 > 0) by lra. nra.
  - intro H. assert (H2 : (x - 3) * (x + 2) > 0) by nra. nra.
Qed.

Lemma lemma_1_4_viii : forall x : R,
  x^2 + x + 1 > 0.
Proof.
  intros x. nra.
Qed.

Axiom PI_gt_3 : PI > 3.

Lemma lemma_1_4_ix : forall x : R,
  (x > -5 /\ x < 3) \/ (x > PI) <-> (x - PI) * (x + 5) * (x - 3) > 0.
Proof.
  intros x. split.
  - intros [[H1 H2] | H3].
    -- assert (x < PI). { pose proof PI_gt_3 as H6. lra. } assert ((x - PI) * (x + 5) < 0) by nra. nra.
    -- assert (x > 3). { pose proof PI_gt_3 as H6. lra. } assert ((x - PI) * (x - 3) > 0) by nra. nra.
  - intro H. pose proof PI_gt_3 as H1. assert (x <=PI \/ x >= PI) by lra. destruct H0 as [H0 | H0].
    -- left. split. assert (x <= -5 \/ x > -5) by lra. destruct H2 as [H2 | H2].
       --- assert ((x - PI) * (x + 5) < 0) by nra. nra.
       --- assert (x < 3 \/ x >= 3) by lra. destruct H3 as [H3 | H3].
           ---- assert ((x - PI) * (x + 5) < 0) by nra. nra.
           ---- apply H2.
      --- assert (x <= 3 \/ x > 3) by lra. destruct H2 as [H2 | H2].
           ---- destruct H2. apply H2. nra.
           ---- destruct H0. assert (H3 : (x - PI) * (x - 3) > 0) by nra. nra. nra.
    -- right. assert (x <= 3 \/ x > 3) by lra. destruct H2 as [H2 | H2].
      --- assert ((x - PI) * (x - 3) < 0) by nra. nra.
           --- destruct H0. auto. nra.
Qed.

Lemma lemma_1_4_x : forall x : R,
  (x > Rpower 2 (1/2) \/ x < Rpower 2 (1/3)) <-> (x - Rpower 2 (1/3)) * (x - Rpower 2 (1/2)) > 0.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- assert (H3 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra). nra.
    -- assert (H3 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra). nra.
  - intro H1. assert (H2 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra).
    pose proof Rtotal_order x (Rpower 2 (1 / 3)) as [H3 | [H3 | H3]].
    -- pose proof Rtotal_order x (Rpower 2 (1 / 2)) as [H4 | [H4 | H4]].
       --- nra.
       --- nra.
       --- nra.
    -- nra.
    -- nra.
Qed.

Lemma lemma_1_4_xi : forall x : R,
  x < 3 <-> Rpower 2 x < 8.
Proof.
  intro x. split.
  - intro H1.  pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- replace 8 with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
       apply Rpower_lt. lra. (simpl; lra).
    -- rewrite H2. rewrite Rpower_O. lra. lra.
    -- replace 8 with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
       apply Rpower_lt. lra. (simpl; lra).
  - intro H1. pose proof Rtotal_order x 3 as [H2 | [H2 | H2]].
    -- apply H2.
    -- rewrite H2 in H1. replace 3 with (INR 3%nat) in H1, H2 by (simpl; lra).
        rewrite Rpower_pow in H1. 2 : { nra. } nra.
    -- assert (8 < Rpower 2 x).
       { replace (8) with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
Qed.

Lemma lemma_1_4_xii : forall x : R,
  x < 1 <-> x + Rpower 3 x < 4.
Proof.
  intro x. split.
  - intro H1. pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- assert (H3 : Rpower 3 (x) < 1). 
       { replace 1 with (Rpower 3 0). 2 : { rewrite Rpower_O. lra. lra. } apply Rpower_lt. lra. lra. } nra.
    -- rewrite H2. rewrite Rpower_O. lra. lra.
    -- assert (H3 : Rpower 3 (x) < 3).
       { replace 3 with (Rpower 3 (INR 1%nat)) at 2. 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
  - intro H1. pose proof Rtotal_order x 1 as [H2 | [H2 | H2]].
    -- apply H2.
    -- rewrite H2 in H1. replace 1 with (INR 1%nat) in H1, H2 by (simpl; lra).
        rewrite Rpower_pow in H1. 2 : { nra. } nra.
    -- assert (3 < Rpower 3 x).
       { replace (3) with (Rpower 3 (INR 1%nat)) at 1. 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
Qed.

Lemma lemma_1_4_xiii : forall x : R,
  0 <= x <= 1 <-> 1 / x + 1 / (1 - x) > 0.
Proof.
  intro x. split.
  - intro H1. destruct H1 as [[H1|H1] [H2|H2]].
    -- assert (H3 : 1 / x > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
       assert (H4 : 1 / (1 - x) > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. } nra.
    -- rewrite H2. replace (1 - 1) with 0 by nra. rewrite Rdiv_0_r. nra.
    -- rewrite <- H1. rewrite Rdiv_1_l. rewrite Rinv_0. nra.
    -- nra.
  - intro H1. pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- pose proof Rtotal_order (1 - x) 0 as [H3 | [H3 | H3]].
       --- nra.
       --- nra.
       --- assert (H4 : 1 / x < 0). { rewrite Rdiv_1_l. apply Rinv_neg. nra. }
           assert (H5 : 1 / (1 - x) > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
           replace (1 / x + 1 / (1 - x)) with (1 / (x * (1 - x))) in H1 by (field; nra).
           assert (H6 : x * (1 - x) < 0) by nra. assert (H7 : 1 / (x * (1 - x)) < 0). 
           { rewrite Rdiv_1_l. apply Rinv_neg. nra. } nra.
    -- nra.
    -- pose proof Rtotal_order (1 - x) 0 as [H3 | [H3 | H3]].
       --- assert (H4 : 1 / x > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
           assert (H5 : 1 / (1 - x) < 0). { rewrite Rdiv_1_l. apply Rinv_neg. nra. }
           replace (1 / x + 1 / (1 - x)) with (1 / (x * (1 - x))) in H1 by (field; nra). 
           assert (H6 : x * (1 - x) < 0) by nra. assert (H7 : 1 / (x * (1 - x)) < 0). 
           { rewrite Rdiv_1_l. apply Rinv_neg. nra. } nra.
       --- nra.
       --- nra.
Qed.

Lemma lemma_1_4_xiv : forall x : R,
  (x > 1 \/ x < -1) <-> (x - 1) / (x + 1) > 0.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- assert (H2 : x - 1 > 0) by lra. assert (H3 : x + 1 > 0) by lra. apply Rdiv_pos_pos. nra. nra.
    -- assert (H3 : x - 1 < 0) by lra. assert (H4 : x + 1 < 0) by lra. apply Rdiv_neg_neg. nra. nra.
  - intro H1. pose proof Rtotal_order x 1 as [H2 | [H2 | H2]].
    -- pose proof Rtotal_order x (-1) as [H3 | [H3 | H3]].
       --- nra.
       --- rewrite H3 in H1. replace (-1 + 1) with (0) in H1 by lra. rewrite Rdiv_0_r in H1. nra.
       --- assert (H4 : x - 1 < 0) by nra. assert (H5 : x + 1 > 0) by nra. assert (H6 : (x - 1) / (x + 1) < 0).
           { apply Rdiv_neg_pos. nra. nra. } nra.
    -- rewrite H2 in H1. replace (1 - 1) with (0) in H1 by lra. rewrite Rdiv_0_l in H1. nra.
    -- pose proof Rtotal_order x (-1) as [H3 | [H3 | H3]].
       --- assert (H4 : x - 1 > 0) by nra. assert (H5 : x + 1 < 0) by nra. assert (H6 : (x - 1) / (x + 1) < 0).
           { apply Rdiv_pos_neg. nra. nra. } nra.
       --- nra.
       --- nra.
Qed.

Lemma lemma_1_5_i : forall a b c d,
  a < b -> c < d -> a + c < b + d.
Proof.
  intros a b c d H1 H2. apply Rplus_lt_compat_l with (r := c) in H1.
  apply Rplus_lt_compat_l with (r := b) in H2. rewrite Rplus_comm with (r2 := b) in H1. 
  rewrite Rplus_comm in H1. apply Rlt_trans with (r2 := b + c). apply H1. apply H2.
Qed.

Lemma lemma_1_5_ii : forall a b,
  a < b -> -b < -a.
Proof.
  intros a b H1. apply Rplus_lt_compat_r with (r := -a) in H1.
  rewrite Rplus_opp_r in H1. apply Rplus_lt_compat_l with (r := -b) in H1.
  rewrite Rplus_0_r in H1. rewrite <- Rplus_assoc in H1. rewrite Rplus_opp_l in H1.
  rewrite Rplus_0_l in H1. apply H1.
Qed.

Lemma lemma_1_5_iii : forall a b c d, 
  a < b -> c > d -> a - c < b - d.
Proof.
  intros a b c d H1 H2. apply Rplus_lt_compat_l with (r := -c) in H1.
  rewrite Rplus_comm in H1. rewrite Rplus_comm with (r2 := b) in H1.
  repeat rewrite <- Rminus_def in H1. assert (H3 : b - c < b - d).
  {
    apply Rgt_lt in H2. apply Rplus_lt_compat_l with (r := -d) in H2.
    apply Rplus_lt_compat_r with (r := b) in H2. apply Rplus_lt_compat_r with (r := -c) in H2.
    replace (-d + d + b + -c) with (b - c) in H2 by lra.
    replace (-d + c + b + -c) with (b - d) in H2 by lra. apply H2.
  }
  apply Rlt_trans with (r2 := b - c).
  - apply H1.
  - apply H3.
Qed.

Lemma lemma_1_5_iv : forall a b c,
  a < b -> c > 0 -> a * c < b * c.
Proof.
  intros a b c H1 H2. apply Rmult_lt_compat_r with (r := c) in H1.
  2 : { apply Rgt_lt in H2. apply H2. } apply H1.
Qed.

Lemma lemma_1_5_v : forall a b c,
  a < b -> c < 0 -> a * c > b * c.
Proof.
  intros a b c H1 H2. pose proof Rtotal_order a 0 as [H3 | [H3 | H3]].
  - pose proof Rtotal_order b 0 as [H4 | [H4 | H4]].
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_gt_compat_r. 2 : { lra. } lra.
    -- rewrite H4. rewrite Rmult_0_l. nra.
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_lt_compat_r. 2 : { lra. } lra.
  - rewrite H3. rewrite Rmult_0_l. nra.
  - pose proof Rtotal_order b 0 as [H4 | [H4 | H4]].
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_lt_compat_r. 2 : { lra. } lra.
    -- rewrite H4. rewrite Rmult_0_l. nra.
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_gt_compat_r. 2 : { lra. } lra.
Qed.

Lemma lemma_1_5_vi : forall a,
  a > 1 -> a ^ 2 > a.
Proof.
  intros a H1. simpl. rewrite Rmult_1_r. rewrite <- Rmult_1_r.
  apply Rlt_gt. rewrite Rmult_comm. apply lemma_1_5_iv. lra. lra.
Qed.

Lemma lemma_1_5_vii : forall a,
  0 < a < 1 -> a ^ 2 < a.
Proof.
  intros a [H1 H2]. simpl. rewrite Rmult_1_r. rewrite <- Rmult_1_r.
  apply Rlt_gt. rewrite <- Rmult_comm with (r1 := 1). apply lemma_1_5_iv. lra. lra.
Qed.

Lemma lemma_1_5_viii : forall a b c d,
  0 <= a < b -> 0 <= c < d -> a * c < b * d.
Proof.
  intros a b c d [H1 H2] [H3 H4]. pose proof Rtotal_order a 0 as [H5 | [H5 | H5]].
  - lra.
  - rewrite H5. rewrite Rmult_0_l. nra.
  - pose proof Rtotal_order c 0 as [H6 | [H6 | H6]].
    -- lra.
    -- rewrite H6. rewrite Rmult_0_r. nra.
    -- assert (H7 : a * c < b * c). { apply lemma_1_5_iv. lra. lra. }
       assert (H8 : b * c < b * d). { rewrite Rmult_comm. rewrite Rmult_comm with (r1 := b).
       apply lemma_1_5_iv. lra. lra. }
       apply Rlt_trans with (r2 := b * c). apply H7. apply H8.
Qed.

Lemma lemma_1_5_ix : forall a b,
  0 <= a < b -> a^2 < b^2.
Proof.
  intros a b [H1 H2]. simpl. repeat rewrite Rmult_1_r. apply lemma_1_5_viii. lra. lra.
Qed.

Lemma lemma_1_5_x : forall a b,
  a >= 0 -> b >= 0 -> a^2 < b^2 -> a < b.
Proof.
  intros a b H1 H2 H3. pose proof Rtotal_order a b as [H4 | [H4 | H4]].
  - apply H4.
  - exfalso. rewrite H4 in H3. apply Rlt_irrefl in H3. apply H3.
  - assert (H5 : b^2 < a^2). { apply lemma_1_5_ix. lra. } 
    assert (H6 : b^2 < b^2). { apply Rlt_trans with (r2 := a^2). apply H5. apply H3. }
    apply Rlt_irrefl in H6. exfalso. apply H6.
Qed.

Lemma Rpow_0 : forall k, 
  (k >= 1)%nat -> 0 ^ k = 0.
Proof.
  intros k H1. destruct k.
  - lia.
  - simpl. lra.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_equ_0 : forall n r,
  r ^ n = 0 -> r = 0.
Proof.
  intros n r. pose proof pow_nonzero r n.
  assert (H1 : r = 0 \/ r <> 0) by apply classic. destruct H1 as [H1 | H1].
  - intros H2. apply H1.
  - intros H2. apply H in H1. apply H1 in H2. exfalso. apply H2.
Qed.

Lemma Rpow_odd_lt_0 : forall x n,
  x < 0 -> (Nat.Odd n -> x^n < 0) /\ (Nat.Even n -> x^n > 0).
Proof.
  intros x n H1. induction n as [| k IH].
  - split.
    -- intro H2. destruct H2 as [k H2]. lia.
    -- intro H2. simpl. lra.
  - destruct IH as [IH1 IH2]. split.
    -- intro H2. simpl. rewrite Nat.Odd_succ in H2. apply IH2 in H2. nra.
    -- intro H2. simpl. rewrite Nat.Even_succ in H2. apply IH1 in H2. nra.
Qed.

Lemma Rpow_even_neg_eq_pos : forall x n,
  x < 0 -> (Nat.Even n -> (-x)^n = x^n) /\ (Nat.Odd n -> (-x)^n = -x^n).
Proof.
  intros x n H1. induction n as [| k IH].
  - simpl. split. reflexivity. intro H3. destruct H3 as [k H3]. lia.
  - simpl. destruct IH as [IH1 IH2]. split.
    -- intro H2. rewrite Nat.Even_succ in H2. rewrite IH2. lra. apply H2.
    -- intro H2. rewrite Nat.Odd_succ in H2. rewrite IH1. lra. apply H2.
Qed.

Lemma abs_smaller_neg_larger : forall x y, x < 0 -> y < 0 -> Rabs y < Rabs x -> x < y.
Proof.
  intros x y Hx Hy Habs.
  unfold Rabs in Habs.
  destruct (Rcase_abs x) as [Hx_neg | Hx_pos].
  - destruct (Rcase_abs y) as [Hy_neg | Hy_pos].
    -- lra.
    -- lra.
  - destruct (Rcase_abs y) as [Hy_neg | Hy_pos].
    -- lra.
    -- lra.
Qed.

Lemma lemma_1_6_a : forall x y n,
  0 <= x < y -> (0 < n)%nat -> x^n < y^n.
Proof.
  intros x y n [H1 H2] H3. induction n as [| k IH].
  - inversion H3.
  - simpl. destruct k as [| k'] eqn:Ek.
    -- simpl. repeat rewrite Rmult_1_r. apply H2.
    -- destruct H1 as [H1 | H1]. 2 : { apply Rmult_ge_0_gt_0_lt_compat. rewrite <- H1. simpl. lra. lra. lra. apply IH. lia. }
       { apply Rmult_gt_0_lt_compat. apply Rpow_gt_0. lra. lra. lra. apply IH. lia. }
Qed.

Lemma lemma_1_6_b : forall x y n,
  x < y -> Nat.Odd n -> x^n < y^n.
Proof.
  intros x y n H1 H2. assert (H3 : x >= 0 \/ x < 0) by lra. destruct H3 as [H3 | H3].
  - apply lemma_1_6_a. split. lra. lra. destruct H2 as [k H2]. lia.
  - pose proof H3 as H3'. apply Rpow_odd_lt_0 with (n := n) in H3. destruct H3 as [H3 H4]. pose proof H2 as H2'.
    apply H3 in H2. assert (H5 : y > 0 \/ y = 0 \/ y < 0) by lra. destruct H5 as [H5 | [H5 | H5]].
    -- assert (H6 : y ^ n > 0). { apply Rpow_gt_0. lra. } nra.
    -- rewrite H5. assert (H6 : (n = 0 \/ n >= 1)%nat) by lia. destruct H6 as [H6 | H6].    
       --- rewrite H6 at 2. simpl. lra.
       --- apply Rpow_0 in H6. rewrite H6. lra.
    -- assert (H6 : (-y)^n < (-x)^n). { apply lemma_1_6_a. split. lra. lra. destruct H2' as [k H2']. lia. }
       assert (H7 : (y)^n < 0). { apply Rpow_odd_lt_0. lra. apply H2'. } replace (-x) with (Rabs x) in H6. 2 : { apply Rabs_left. apply H3'. }
       replace (-y) with (Rabs y) in H6. 2 : { apply Rabs_left. apply H5. } repeat rewrite RPow_abs in H6. 
       apply abs_smaller_neg_larger; assumption.
Qed.

Lemma lemma_1_6_c : forall x y n,
  x ^ n = y ^ n -> Nat.Odd n -> x = y.
Proof.
  intros x y n H1 H2. pose proof Rtotal_order x y as H3. destruct H3 as [H3 | [H3 | H3]].
  - pose proof lemma_1_6_b x y n as H4. apply H4 in H3. 2 : { apply H2. } lra.
  - apply H3.
  - pose proof lemma_1_6_b y x n as H4. apply H4 in H3. 2 : { apply H2. } lra.
Qed.

Lemma lemma_1_6_d : forall x y n,
  x ^ n = y ^ n -> Nat.Even n -> (0 < n)%nat -> (x = y \/ x = -y).
Proof.
  intros x y n H1 H2 H3. 
  assert (H4 : (x >= 0 /\ y >= 0) \/ (x < 0 /\ y < 0) \/ (x >= 0 /\ y < 0) \/ (x < 0 /\ y >= 0)) by lra. 
  destruct H4 as [H4 | [H4 | [H4 | H4]]].
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a x y n as H7. assert (H8 : 0 <= x < y) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. apply H6.
    -- pose proof lemma_1_6_a y x n as H7. assert (H8 : 0 <= y < x) by lra. apply H7 in H8. 2 : { apply H3. } lra.
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- assert (H7 : -x > 0 /\ -y > 0 /\ -x > -y) by lra. destruct H7 as [H7 [H8 H9]]. pose proof lemma_1_6_a (-y) (-x) n as H10.
       assert (H11 : 0 <= -y < -x) by lra. apply H10 in H11. 2 : { apply H3. }  pose proof Rpow_even_neg_eq_pos (x) n as H12.
       destruct H12 as [H12 H13]. apply H4. pose proof H2 as H2'. apply H12 in H2. rewrite <- H2 in H1. pose proof Rpow_even_neg_eq_pos (y) n as H14.
       destruct H14 as [H14 H15]. apply H5. apply H14 in H2'. rewrite <- H2' in H1. lra.
    -- left. apply H6.
    -- assert (H7 : -x > 0 /\ -y > 0 /\ -x < -y) by lra. destruct H7 as [H7 [H8 H9]]. pose proof lemma_1_6_a (-x) (-y) n as H10.
       assert (H11 : 0 <= -x < -y) by lra. apply H10 in H11. 2 : { apply H3. }  pose proof Rpow_even_neg_eq_pos (y) n as H12.
       destruct H12 as [H12 H13]. apply H5. pose proof H2 as H2'. apply H12 in H2. rewrite <- H2 in H1. pose proof Rpow_even_neg_eq_pos (x) n as H14.
       destruct H14 as [H14 H15]. apply H4. apply H14 in H2'. rewrite <- H2' in H1. lra.
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a x y n as H7. assert (H8 : 0 <= x < y) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. apply H6.
    -- right. pose proof Rtotal_order x (-y) as H7. destruct H7 as [H7 | [H7 | H7]].
       --- pose proof lemma_1_6_a x (-y) n as H8. assert (H9 : 0 <= x < -y) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-y)^n = y^n). { pose proof Rpow_even_neg_eq_pos y n as H10. destruct H10 as [H10 H11]. apply H5. apply H10. apply H2. } lra.
       --- apply H7.
       --- pose proof lemma_1_6_a (-y) x n as H8. assert (H9 : 0 <= -y < x) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-y)^n = y^n). { pose proof Rpow_even_neg_eq_pos y n as H10. destruct H10 as [H10 H11]. apply H5. apply H10. apply H2. } lra.
- destruct H4 as [H4 H5]. pose proof Rtotal_order y x as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a y x n as H7. assert (H8 : 0 <= y < x) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. auto.
    -- right. pose proof Rtotal_order y (-x) as H7. destruct H7 as [H7 | [H7 | H7]].
       --- pose proof lemma_1_6_a y (-x) n as H8. assert (H9 : 0 <= y < -x) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-x)^n = x^n). { pose proof Rpow_even_neg_eq_pos x n as H10. destruct H10 as [H10 H11]. apply H4. apply H10. apply H2. } lra.
       --- lra.
       --- pose proof lemma_1_6_a (-x) y n as H8. assert (H9 : 0 <= -x < y) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-x)^n = x^n). { pose proof Rpow_even_neg_eq_pos x n as H10. destruct H10 as [H10 H11]. apply H4. apply H10. apply H2. } lra.
Qed.

Lemma lemma_1_7 : forall a b : R,
  (0 < a < b) -> a < sqrt (a * b) < (a + b) / 2 /\ (a + b) / 2 < b.
Proof.
  intros a b [H1 H2]. split.
  - split.
    -- pose proof sqrt_square a as H3. rewrite <- H3 at 1. 2 : { lra. } apply sqrt_lt_1. nra. nra. nra.
    -- rewrite <- sqrt_square. 2 : { nra. } apply sqrt_lt_1. nra. nra. nra.
  - nra.
Qed.

Definition one_and_only_one_3 (P1 P2 P3 : Prop) : Prop :=
  (P1 /\ ~ P2 /\ ~ P3) \/ (~ P1 /\ P2 /\ ~ P3) \/ (~ P1 /\ ~ P2 /\ P3).

Definition P10' := forall a b : R, one_and_only_one_3 (a = b) (a < b) (b < a). 
Definition P11' := forall a b c : R, (a < b /\ b < c) -> a < c.
Definition P12' := forall a b c : R, a < b -> a + c < b + c.
Definition P13' := forall a b c : R, a < b /\ 0 < c -> a * c < b * c.

Definition P10 := forall (P : R -> Prop) (a : R),
  (forall r : R, P r <-> 0 < r) -> one_and_only_one_3 (a = 0) (P a) (P (-a)).

Definition P11 := forall (P : R -> Prop) (a b : R),
  (forall r : R, P r <-> 0 < r) -> (P a /\ P b) -> P (a + b).

Definition P12 := forall (P : R -> Prop) (a b : R),
  (forall r : R, P r <-> 0 < r) -> (P a /\ P b) -> P (a * b).

Theorem Rplus_neg_neg : P11' -> P12' -> forall a b : R, a < 0 -> b < 0 -> a + b < 0.
Proof.
  intros H1 H2 a b H3 H4. unfold P11', P12' in H1, H2. specialize H2 with (a := a) (b := 0) (c := b).
  rewrite Rplus_0_l in H2. apply H2 in H3. apply H1 with (a := a + b) (b := b) (c := 0).
  split. apply H3. apply H4.
Qed.

Theorem Rplus_pos_pos : P11' -> P12' -> forall a b : R, a > 0 -> b > 0 -> a + b > 0.
Proof.
  intros H1 H2 a b H3 H4. unfold P11', P12' in H1, H2. specialize H2 with (a := 0) (b := a) (c := b).
  rewrite Rplus_0_l in H2. apply H2 in H3. apply Rlt_gt. apply H1 with (a := 0) (b := b) (c := a + b).
  split. apply Rgt_lt. apply H4. apply H3.
Qed.

Lemma Ropp_gt_lt_0_contravar' : P10' -> P11' -> P12' -> forall a, a < 0 <-> -a > 0.
Proof.
  intros H1 H11 H12 a. split.
  {
    intros H2.
    unfold P10' in H1. pose proof H1 as H1'. specialize H1 with (a := a + (-a)) (b := 0).
    unfold one_and_only_one_3 in H1. destruct H1 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    - unfold not in *. assert (H6 : (-a < 0 -> False) /\ (-a = 0 -> False)). 
      -- split.
        --- intro H6. apply H4. apply Rplus_neg_neg; assumption.
        --- intro H6. apply H4. rewrite H6. rewrite Rplus_0_r. apply H2.
      -- destruct H6 as [H6 H7]. specialize H1' with (a := -a) (b := 0). unfold one_and_only_one_3 in H1'.
        destruct H1' as [[H8 [H9 H10]] | [[H8 [H9 H10]] | [H8 [H9 H10]]]].
        --- unfold not in *. apply H7 in H8. exfalso. apply H8.
        --- apply H6 in H9. exfalso. apply H9.
        --- apply H10.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
  }
  {
    intros H2.
    unfold P10' in H1. pose proof H1 as H1'. specialize H1 with (a := a + (-a)) (b := 0).
    unfold one_and_only_one_3 in H1. destruct H1 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    - unfold not in *. assert (H6 : (a > 0 -> False) /\ (a = 0 -> False)). 
      -- split.
        --- intros H6. apply H5. apply Rplus_pos_pos; assumption.
        --- intros H6. apply H5. rewrite H6 at 1. rewrite Rplus_0_l. apply Rgt_lt. apply H2.
      -- destruct H6 as [H6 H7]. specialize H1' with (a := a) (b := 0). unfold one_and_only_one_3 in H1'.
        destruct H1' as [[H8 [H9 H10]] | [[H8 [H9 H10]] | [H8 [H9 H10]]]].
        --- unfold not in *. apply H7 in H8. exfalso. apply H8.
        --- apply H9.
        --- exfalso. apply H6 in H10. apply H10.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
  } 
Qed.

Lemma lemma_1_8_P10 : P10' -> P11' -> P12' -> P10.
Proof.
  intros H1 H11 H12. unfold P10. intros P a. pose proof H1 as H1'. unfold P10' in H1. intros H2.
  unfold one_and_only_one_3 in *. specialize H1 with (a := a) (b := 0).
  destruct H1 as [[H1 [H3 H4]] | [[H1 [H3 H4]] | [H1 [H3 H4]]]].
  - left. split.
    -- apply H1.
    -- split.
      --- unfold not. intro H5. specialize H2 with (r := a). apply H2 in H5. unfold not in H4. apply H4 in H5. apply H5.
      --- unfold not. intro H5. specialize H2 with (r := -a). apply H2 in H5. unfold not in H3. apply Rlt_gt in H5. 
          apply Ropp_gt_lt_0_contravar' in H5; try apply H3; assumption.
  - right. right. split.
    -- apply H1.
    -- split.
      --- specialize H2 with (r := a). unfold not in *. intro H5. apply H2 in H5. apply H4 in H5. apply H5.
      --- specialize H2 with (r := -a). apply Ropp_gt_lt_0_contravar' in H3; try apply H2; assumption.
  - right. left. split.
    -- apply H1.
    -- split.
      --- specialize H2 with (r := a). apply H2 in H4. apply H4.
      --- specialize H2 with (r := -a). unfold not in *. intro H5. apply H2 in H5. apply Ropp_gt_lt_0_contravar' in H5; try apply H3; assumption. 
Qed.

Lemma lemma_1_8_P11 : (P11' /\ P12') -> P11.
Proof.
  intros [H1 H2]. unfold P11. intros P a b H3 [H4 H5].
  unfold P11', P12' in H1, H2. apply H3 in H4. apply H3 in H5.
  assert (H6 : forall r1 r2 r3 r4, r1 < r2 /\ r3 < r4 -> r1 + r3 < r2 + r3 < r2 + r4).
  - intros r1 r2 r3 r4 [H6 H7]. split.
    -- apply H2. apply H6.
    -- rewrite Rplus_comm. rewrite Rplus_comm with (r1 := r2). apply H2. apply H7.
  - specialize (H6 0 a 0 b). destruct H6 as [H6 H7]. (split; try apply H4; apply H5).
    specialize (H1 (0 + 0) (a + 0) (a + b)). rewrite Rplus_0_l in*.
    assert (H8 : 0 < a + b). { apply H1. split. apply H6. apply H7. }
    apply H3. apply H8.
Qed.

Lemma lemma_1_8_P12 : P13' -> P12.
Proof.
  intros H1. unfold P13', P12 in *. intros P a b H2 [H3 H4].
  apply H2 in H3. apply H2 in H4. specialize H1 with (a := 0) (b := a) (c := b).
  assert (H5 : 0 < a /\ 0 < b) by (split; assumption). apply H1 in H5. 
  rewrite Rmult_0_l in H5. apply H2 in H5. apply H5.
Qed.

Ltac solve_abs := 
  try intros; repeat unfold Rabs in *; repeat destruct Rcase_abs in *; try nra; try field; try nia.

Lemma lemma_1_9_i : Rabs (sqrt 2 + sqrt 3 - sqrt 5 + sqrt 7) = sqrt 2 + sqrt 3 - sqrt 5 + sqrt 7.
Proof.
  solve_abs.
  assert (H1 : sqrt 7 > sqrt 5) by (apply sqrt_lt_1; lra).
  assert (H2 : sqrt 2 > 0) by (apply sqrt_lt_R0; lra).
  assert (H3 : sqrt 3 > 0) by (apply sqrt_lt_R0; lra).
  assert (H4 : sqrt 5 > 0) by (apply sqrt_lt_R0; lra).
  lra.
Qed.

Lemma lemma_1_9_ii : forall a b,
  Rabs (Rabs (a + b) - Rabs a - Rabs b) = Rabs a + Rabs b - Rabs (a + b).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_9_iii : forall a b c,
  Rabs (Rabs (a + b) + Rabs c - Rabs (a + b + c)) = Rabs (a + b) + Rabs c - Rabs (a + b + c).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_9_iv : forall x y,
  Rabs (x^2 - 2 * x * y + y^2) = x^2 - 2 * x * y + y^2.
Proof.
  solve_abs.
  assert (x * x + y * y > 2 * x * y) by (pose proof Rtotal_order x y as [H1 | [H1 | H1]]; nra); nra.
Qed.

Lemma sqrt_inequality: sqrt 3 + sqrt 5 > sqrt 7.
Proof.
  apply Rlt_gt.
  assert (H1 : sqrt 7 > 0) by (apply sqrt_lt_R0; lra).
  assert (H2 : sqrt 5 > 0) by (apply sqrt_lt_R0; lra).
  assert (H3 : sqrt 3 > 0) by (apply sqrt_lt_R0; lra).
  assert (H: (sqrt 3 + sqrt 5) ^ 2 > (sqrt 7) ^ 2).
  - simpl. repeat rewrite Rmult_1_r. rewrite sqrt_def. 2 : { lra. }
    replace ((sqrt 3 + sqrt 5) * (sqrt 3 + sqrt 5)) with (sqrt 3 * sqrt 3 + 2 * sqrt 3 * sqrt 5 + sqrt 5 * sqrt 5) by lra.
    repeat rewrite sqrt_def; try nra.
  - nra.
Qed.

Lemma lemma_1_9_v : Rabs (Rabs (sqrt 2 + sqrt 3) - Rabs (sqrt 5 - sqrt 7)) = sqrt 2 + sqrt 3 + sqrt 5 - sqrt 7.
Proof.
  assert (H1 : sqrt 7 > sqrt 5) by (apply sqrt_lt_1; lra).
  assert (H2 : sqrt 2 > 0) by (apply sqrt_lt_R0; lra).
  assert (H3 : sqrt 3 > 0) by (apply sqrt_lt_R0; lra).
  assert (H4 : sqrt 5 > 0) by (apply sqrt_lt_R0; lra).
  pose proof sqrt_inequality as H5.
  unfold Rabs. repeat destruct Rcase_abs; try nra.
Qed.

Lemma Rminus_neg : forall a b,
  a - - b = a + b.
Proof.
  intros a b. lra.
Qed.

Lemma Rplus_neg : forall a b,
  a + - b = a - b.
Proof. 
  intros a b. lra.
Qed.

Lemma lemma_1_10_i : forall a b,
  ((a >= -b /\ b >= 0) -> Rabs (a + b) - Rabs b = a) /\
  ((a <= -b /\ b <= 0) -> Rabs (a + b) - Rabs b = -a) /\
  ((a >= -b /\ b <= 0) -> Rabs (a + b) - Rabs b = a + 2 * b) /\
  ((a <= -b /\ b >= 0) -> Rabs (a + b) - Rabs b = -a - 2 * b).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_10_ii : forall x,
  (x >= 1 <-> Rabs (Rabs x - 1) = x - 1) /\
  (0 <= x <= 1 <-> Rabs (Rabs x - 1) = 1 - x) /\
  (-1 <= x <= 0 <-> Rabs (Rabs x - 1) = 1 + x) /\
  (x <= -1 <-> Rabs (Rabs x - 1) = -1 - x).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_10_iii : forall x,
  (x >= 0 <-> Rabs x - Rabs (x^2) = x - x^2) /\
  (x <= 0 <-> Rabs x - Rabs (x^2) = -x - x^2).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_10_iv : forall a,
  (a >= 0 <-> a - Rabs (a - Rabs a) = a) /\
  (a <= 0 <-> a - Rabs (a - Rabs a) = 3 * a).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_i : forall x, 
  (x = 11 \/ x = -5) <-> Rabs (x - 3) = 8.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_ii : forall x,
  (-5 < x < 11) <-> Rabs (x - 3) < 8.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_iii : forall x,
  (-6 < x < -2) <-> Rabs (x + 4) < 2.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_iv : forall x,
  (x < 1 \/ x > 2) <-> Rabs (x - 1) + Rabs (x - 2) > 1.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_v : forall x, Rabs (x - 1) + Rabs (x + 1) < 2 -> False.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_vi : forall x, Rabs (x - 1) + Rabs (x + 1) < 1 -> False.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_vii : forall x, 
  (x = 1 \/ x = -1) <-> Rabs (x - 1) * Rabs (x + 1) = 0.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_11_viii : forall x,
 (x = (-1 + sqrt 21) / 2 \/ x = (-1 - sqrt 21) / 2) <-> Rabs (x - 1) * Rabs (x + 2) = 3.
Proof.
  intros x. assert (H1 : x^2 + x - 5 = 0 <-> x = (-1 + sqrt 21) / 2 \/ x = (-1 - sqrt 21) / 2).
  {
    split.
    {
    intros H1. replace (x^2 + x - 5) with ((x - (-1 + sqrt 21) / 2) * (x - (-1 - sqrt 21) / 2)) in H1. 2 :
       {
         set (r1 := (-1 + sqrt 21) / 2). set (r2 := (-1 - sqrt 21) / 2). replace ((x - r1) * (x - r2)) with (x^2 - x * (r2 + r1) + r1 * r2) by lra.
         assert (H2 : r1 + r2 = -1).
        { unfold r1, r2. apply Rmult_eq_reg_r with (r := 2). 2 : { lra. } nra. }
         assert (H3 : r1 * r2 = -5). 
         {
            unfold r1, r2. apply Rmult_eq_reg_r with (r := 4). 2 : { lra. }
            replace (((-1 + sqrt 21) / 2) * ((-1 - sqrt 21) / 2) * 4) with ((-1 - sqrt 21) * (-1 + sqrt 21)) by nra.
            replace (-5 * 4) with (-20) by lra. replace ((-1 - sqrt 21) * (-1 + sqrt 21)) with (1^2 - (sqrt 21)^2) by lra.
            rewrite pow2_sqrt. lra. lra.
         } nra.
       } nra. 
    }
    {
     intros H1. destruct H1 as [H1 | H1].
     {
       rewrite H1. apply Rplus_eq_reg_r with (r := 5). rewrite Rplus_0_l.
       replace (((-1 + sqrt 21) / 2) ^ 2 + (-1 + sqrt 21) / 2 - 5 + 5) with (((-1 + sqrt 21) / 2) * (((-1 + sqrt 21) / 2) + 1)) by nra.
       apply Rmult_eq_reg_r with (r := 4). 2 : { lra. } replace ((-1 + sqrt 21) / 2 * ((-1 + sqrt 21) / 2 + 1) * 4) with ((-1 + sqrt 21) * (-1 + sqrt 21 + 2)) by nra.
       replace (5 * 4) with 20 by lra. replace (-1 + sqrt 21 + 2) with (1 + sqrt 21) by lra. replace ((-1 + sqrt 21) * (1 + sqrt 21)) with (-1 + (sqrt 21)^2) by nra.
       rewrite pow2_sqrt. lra. lra.
     }
     {
      rewrite H1. apply Rplus_eq_reg_r with (r := 5). rewrite Rplus_0_l.
      replace (((-1 - sqrt 21) / 2) ^ 2 + (-1 - sqrt 21) / 2 - 5 + 5) with (((-1 - sqrt 21) / 2) * (((-1 - sqrt 21) / 2) + 1)) by nra.
      apply Rmult_eq_reg_r with (r := 4). 2 : { lra. } replace ((-1 - sqrt 21) / 2 * ((-1 - sqrt 21) / 2 + 1) * 4) with ((-1 - sqrt 21) * (-1 - sqrt 21 + 2)) by nra.
      replace (5 * 4) with 20 by lra. replace (-1 - sqrt 21 + 2) with (1 - sqrt 21) by lra. replace ((-1 - sqrt 21) * (1 - sqrt 21)) with (-1 + (sqrt 21)^2) by nra.
      rewrite pow2_sqrt. lra. lra.
     }
    } 
  } solve_abs. 
Qed.

Lemma lemma_1_12_i : forall x y,
  Rabs (x * y) = Rabs x * Rabs y.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_12_ii : forall x,
  Rabs (1 / x) = 1 / Rabs x.
Proof.
  intros x. pose proof Rinv_neg x. pose proof Rinv_pos x. 
  solve_abs. nra.  
  unfold Rdiv. destruct r0. nra.
  rewrite H1. unfold Rdiv. rewrite Rinv_0. nra.
Qed.

Lemma lemma_1_12_iii : forall x y,
  y <> 0 -> Rabs x / Rabs y = Rabs (x / y).
Proof.
  intros x y H1. pose proof Rinv_neg y. pose proof Rinv_pos y.
  solve_abs. nra. nra. destruct r. nra. nra. 
Qed.

Lemma lemma_1_12_iv : forall x y,
  Rabs (x - y) <= Rabs x + Rabs y.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_12_v : forall x y,
  Rabs x - Rabs y <= Rabs (x - y).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_12_vi : forall x y,
  Rabs ((Rabs x) - (Rabs y)) <= Rabs (x - y).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_12_vii : forall x y z,
  Rabs (x + y + z) <= Rabs x + Rabs y + Rabs z.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_12_viii' : forall x y z,
  Rabs (x + y + z) = Rabs x + Rabs y + Rabs z <-> (x >= 0 /\ y >= 0 /\ z >= 0) \/ (x <= 0 /\ y <= 0 /\ z <= 0).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_13_max : forall x y,
  Rmax x y = (x + y + Rabs (x - y)) / 2.
Proof.
  intros x y. unfold Rmax. destruct (Rle_dec x y) as [H1 | H1].
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- lra.
    -- assert (H3 : x = y) by lra. rewrite H3. lra.
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- assert (H3 : x < y) by lra. assert (H4 : x > y) by lra. lra.
    -- lra.
Qed.

Lemma lemma_1_13_min : forall x y,
  Rmin x y = (x + y - Rabs (x - y)) / 2.
Proof.
  intros x y. unfold Rmin. destruct (Rle_dec x y) as [H1 | H1].
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- lra.
    -- assert (H3 : x = y) by lra. rewrite H3. lra.
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- assert (H3 : x < y) by lra. assert (H4 : x > y) by lra. lra.
    -- lra.
Qed.

Definition Rmax_3 (x y z : R) : R :=
  Rmax (Rmax x y) z.

Definition Rmin_3 (x y z : R) : R :=
  Rmin (Rmin x y) z.

Lemma lemma_1_13_max' : forall x y z,
  Rmax_3 x y z = (x + ((y + z + Rabs (y - z)) / 2) + Rabs (((y + z + Rabs (y - z)) / 2) - x)) / 2.
Proof.
  intros x y z.
  repeat unfold Rmax_3; repeat unfold Rmax; repeat destruct Rle_dec; solve_abs.
Qed.

Lemma lemma_1_13_min' : forall x y z,
  Rmin_3 x y z = (x + ((y + z - Rabs (y - z)) / 2) - Rabs (((y + z - Rabs (y - z)) / 2) - x)) / 2.
Proof.
  intros x y z.
  repeat unfold Rmin_3, Rmin; repeat destruct Rle_dec; solve_abs.
Qed.

Lemma lemma_1_14_a : forall a,
  Rabs a = Rabs (-a).
Proof.
  solve_abs.
Qed.

Lemma lemma_1_14_b : forall a b,
  -b <= a <= b <-> Rabs a <= b.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_14_b' : forall a,
  - Rabs a <= a <= Rabs a.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_14_c : forall a b,
  Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros a b. pose proof lemma_1_14_b' a as H1. pose proof lemma_1_14_b' b as H2.
  assert (H3 : -(Rabs a + Rabs b) <= a + b <= Rabs a + Rabs b) by lra.
  pose proof lemma_1_14_b (a + b) (Rabs a + Rabs b) as [H4 H5]. apply H4. apply H3.
Qed.

Lemma lemma_1_15' : forall x y,
  x <> 0 -> x^2 + x * y + y^2 > 0 /\ x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 > 0.
Proof.
  intros x y H1. split.
  - pose proof Req_dec x y as [H2 | H2].
    -- rewrite H2 in *. rewrite <- Rsqr_def. pose proof Rsqr_pos_lt y as H3.
       apply H3 in H1. nra.
    -- assert (H3 : x^2 + x * y + y^2 = (x^3 - y^3) / (x - y)) by (field; lra).
       assert (H4 : (x - y) > 0 -> x^3 - y^3 > 0). 
       {
         intro H4. apply Rplus_gt_reg_r with (r := y^3). 
         replace (x^3 - y^3 + y^3) with (x^3) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 1%nat. lia.
       } 
       assert (H5 : (x - y) < 0 -> x^3 - y^3 < 0). 
       {
         intro H5. apply Rplus_lt_reg_r with (r := y^3). 
         replace (x^3 - y^3 + y^3) with (x^3) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 1%nat. lia.
       }
       nra.
  - pose proof Req_dec x y as [H2 | H2].
    -- rewrite H2 in *. replace (y ^ 4 + y ^ 3 * y + y ^ 2 * y ^ 2 + y * y ^ 3 + y ^ 4) with (5 * y^2 * y^2) by nra.
       assert (H3 : 0 < y^2) by nra. nra.
    -- assert (H3 : x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 = (x^5 - y^5) / (x - y)) by (field; lra).
       assert (H4 : (x - y) > 0 -> x^5 - y^5 > 0). 
       {
         intro H4. apply Rplus_gt_reg_r with (r := y^5). 
         replace (x^5 - y^5 + y^5) with (x^5) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 2%nat. lia.
       } 
       assert (H5 : (x - y) < 0 -> x^5 - y^5 < 0). 
       {
         intro H5. apply Rplus_lt_reg_r with (r := y^5). 
         replace (x^5 - y^5 + y^5) with (x^5) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 2%nat. lia.
       }
       nra.
Qed.

Lemma lemma_1_15 : forall x y,
  (x <> 0 \/ y <> 0) -> x^2 + x * y + y^2 > 0 /\ x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 > 0.
Proof.
  intros x y [H1 | H1].
  - apply lemma_1_15'. apply H1.
  - pose proof lemma_1_15' y x as H2. nra.
Qed.

Lemma lemma_1_16_a : forall x y,
  (x = 0 \/ y = 0) <-> (x + y)^2 = x^2 + y^2.
Proof.
  intros x y. split.
  - intros [H1 | H1].
    -- rewrite H1. lra.
    -- rewrite H1. lra.
  - intros H1. nra.
Qed.

Lemma lemma_1_16_b' : forall x y,
  (x <> 0) -> 4 * x^2 + 6 * x * y + 4 * y^2 > 0.
Proof.
  intros x y H1.
  assert (H2 : x^2 + 2 * x * y + y^2 >= 0).
  { replace (x^2 + 2 * x * y + y^2) with ((x + y)^2) by lra. apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : 4 * x^2 + 8 * x * y + 4 * y^2 >= 0) by nra.
  assert (H4 : 4 * x^2 + 6 * x * y + 4 * y^2 <= 0 \/ 4 * x^2 + 6 * x * y + 4 * y^2 > 0) by lra. destruct H4 as [H4 | H4].
  - assert (H5 : 2 * x * y > 0) by nra. assert (H6 : y <> 0) by nra. assert (H7 : 4 * x^2 + 6 * x * y + 4 * y^2 > 0) by nra.
    apply H7.
  - apply H4.
Qed.

Lemma lemma_1_16_b : forall x y,
  (x <> 0 \/ y <> 0) -> 4 * x^2 + 6 * x * y + 4 * y^2 > 0.
Proof.
  intros x y [H1 | H1].
  - apply lemma_1_16_b'. apply H1.
  - pose proof lemma_1_16_b' y x as H2. nra.
Qed.

Lemma lemma_1_16_c : forall x y,
  (x + y)^4 = (x^4 + y^4) <-> (x = 0 \/ y = 0).
Proof.
  intros x y. split.
  - intros H1. assert (H2 : (x + y)^4 = (x^4 + 4 * x^3 * y + 6 * x^2 * y^2 + 4 * x * y^3 + y^4)) by nra.
    assert (H3 : (x + y)^4 = x * y * (4 * x^2 + 6 * x * y + 4 * y^2) + (x^4 + y^4)) by nra.
    pose proof lemma_1_16_b x y as H4. assert (H5 : x = 0 \/ y = 0 \/ (x <> 0 \/ y <> 0)) by tauto.
    destruct H5 as [H5 | [H5 | H5]].
    -- auto.
    -- auto.
    -- apply H4 in H5. assert (H6 : (x * y = 0 \/ (4 * x ^ 2 + 6 * x * y + 4 * y ^ 2 = 0))) by nra. nra.
  - intros [H1 | H1].
    -- rewrite H1. lra.
    -- rewrite H1. lra.
Qed.

Lemma Rpow_eq_0 : forall x n,
  x ^ n = 0 -> x = 0.
Proof.
  intros x n. induction n as [| k IH].
  - nra.
  - intro H1. simpl in H1. apply Rmult_integral in H1. destruct H1 as [H1 | H1].
    -- apply H1.
    -- apply IH. apply H1.
Qed.

Lemma lemma_1_16_d : forall x y,
  (x + y)^5 = (x^5 + y^5) <-> (x = 0 \/ y = 0 \/ x = -y).
Proof.
  intros x y. split.
  - intro H1. assert (H2 : (x + y)^5 = (x^5 + 5 * x^4 * y + 10 * x^3 * y^2 + 10 * x^2 * y^3 + 5 * x * y^4 + y^5)) by nra.
    assert (H3 : (x + y)^5 = x * y * (5 * x^3 + 10 * x^2 * y + 10 * x * y^2 + 5 * y^3) + (x^5 + y^5)) by nra.
    assert (H5 : x = 0 \/ y = 0 \/ (x <> 0 \/ y <> 0)) by tauto. destruct H5 as [H5 | [H5 | H5]].
    -- auto.
    -- auto.
    -- assert (H6 : (x * y = 0 \/ (x ^ 3 + 2 * x ^ 2 * y + 2 * x * y ^ 2 + y ^ 3 = 0))) by nra.
       destruct H6 as [H6 | H6].
       --- nra.
       --- assert (H7 : (x + y)^3 = x^3 + 3 * x^2 * y + 3 * x * y^2 + y^3) by nra.
           assert (H8 : (x + y)^3 = x^2 * y + x * y^2) by nra.
           assert (H9 : (x + y)^3 = x * y * (x + y)) by nra.  
           assert (H10 : x + y = 0 \/ (x + y)^2 = x * y) by nra. destruct H10 as [H10 | H10].
           ---- nra.
           ---- replace ((x + y)^2) with (x^2 + 2 * x * y + y^2) in H10 by nra.
                assert (x^2 + x * y + y^2 = 0) by nra. apply lemma_1_15 in H5. destruct H5 as [H5 H11].
                rewrite H in H5. apply Rlt_irrefl in H5. exfalso. apply H5.
  - nra.
Qed.

Lemma lemma_1_17_a : forall x,
  (x = 3 / 4 -> 2 * x^2 - 3 * x + 4 = 23 / 8) /\ 23 / 8 <= 2 * x^2 - 3 * x + 4.
Proof.
  intros x. split.
  - intro H1. rewrite H1. nra.
  - replace (2 * x^2 - 3 * x + 4) with (2 * (x - 3 / 4)^2 + 23 / 8) by nra.
    assert (H1 : (x - 3 / 4)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed.

Lemma lemma_1_17_b : forall x y,
  (x = 3 / 2 /\ y = -1 -> x^2 - 3 * x + 2 * y^2 + 4 * y + 2 = -9 / 4) /\ -9 / 4 <= x^2 - 3 * x + 2 * y^2 + 4 * y + 2.
Proof.
  intros x y. split.
  - intros [H1 H2]. rewrite H1, H2. nra.
  - replace (x^2 - 3 * x + 2 * y^2 + 4 * y + 2) with ((x - 3 / 2)^2 + 2 * (y + 1)^2 - 9 / 4) by nra.
    assert (H1 : (x - 3 / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H2 : (y + 1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed.

Lemma lemma_1_17_c : forall x y,
  ((x = 4 /\ y = -1) -> x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7 = 2) /\ 2 <= x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7.
Proof.
  intros x y. split.
  - intros [H1 H2]. rewrite H1, H2. nra.
  - replace (x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7) with ((x + 2 * y - 2)^2 + (y + 1)^2 + 2) by nra.
    assert (H1 : (x + 2 * y - 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H2 : (y + 1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed. 

Lemma lemma_1_18_a : forall b c x,
  (b^2 - 4 * c >= 0) -> ((x = (-b + sqrt (b^2 - 4 * c))/ 2 \/ x = (-b - sqrt (b^2 - 4 * c))/ 2)) -> x^2 + b * x + c = 0.
Proof.
  intros b c x H1 [H2 | H2].
  - rewrite H2. replace (((- b + sqrt (b ^ 2 - 4 * c)) / 2) ^ 2) with ((b^2 - 2 * b * sqrt (b^2 - 4 * c) + (sqrt (b^2 - 4 * c))^2) / 4) by nra.
    simpl. repeat rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { lra. } nra.
  - rewrite H2. replace (((- b - sqrt (b ^ 2 - 4 * c)) / 2) ^ 2) with ((b^2 + 2 * b * sqrt (b^2 - 4 * c) + (sqrt (b^2 - 4 * c))^2) / 4) by nra.
    simpl. repeat rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { lra. } nra.
Qed.

Lemma lemma_1_18_a' : forall b c,
  b^2 - 4 * c >= 0 -> (exists x, x^2 + b * x + c = 0).
Proof.
  intros b c H1.
  exists ((-b + sqrt (b^2 - 4 * c)) / 2).
  apply lemma_1_18_a; auto.
Qed.

Lemma lemma_1_18_a'' : forall b c,
  (forall x, x^2 + b * x + c <> 0) -> b^2 - 4 * c < 0.
Proof.
  intros b c H1.
  assert (H2 : b^2 - 4 * c >= 0 \/ b^2 - 4 * c < 0) by nra. destruct H2 as [H2 | H2].
  - exfalso. apply lemma_1_18_a' in H2. destruct H2 as [x H2]. unfold not in H1. specialize (H1 x). 
    apply H1. apply H2.
  - apply H2.
Qed.

Lemma lemma_1_18_b : forall b c x,
  (b^2 - 4 * c < 0) -> x^2 + b * x + c > 0.
Proof.
  intros b c x H1. replace (x^2 + b * x + c) with ((x + b / 2)^2 + (c - b^2 / 4)) by nra.
  assert (H2 : (x + b / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : (c - b^2 / 4) > 0). { nra. } nra.
Qed.

Lemma lemma_1_18_c : forall x y,
  (x <> 0 \/ y <> 0) -> x^2 + x * y + y^2 > 0.
Proof.
  intros x y [H1 | H1].
  - replace (x^2 + x * y + y^2) with (y^2 + x * y + x^2) by nra. apply lemma_1_18_b. nra.  
  - rewrite Rmult_comm with (r1 := x) (r2 := y). apply lemma_1_18_b. nra.
Qed.

Lemma lemma_1_18_d : forall x y a,
  (x <> 0 \/ y <> 0) -> a^2 < 4 -> x^2 + a * x * y + y^2 > 0.
Proof.
  intros x y a [H1 | H1].
  - intro H2. replace (x^2 + a*x * y + y^2) with (y^2 + a * x * y + x^2) by nra. apply lemma_1_18_b. assert (H3 : x^2 > 0) by nra. nra.
  - intro H2. replace (x^2 + a * x * y + y^2) with ((x + a * y / 2)^2 + (y^2 - a^2 * y^2 / 4)) by nra.
    assert (H3 : (x + a * y / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    replace (y^2 - a^2 * y^2 / 4) with (y^2 * (1 - a^2 / 4)) by nra. assert (H4 : y^2 > 0) by nra. nra.
Qed.

Lemma lemma_1_18_d' : forall a, a^2 >= 4 -> exists x y, (x <> 0 \/ y <> 0) -> x^2 + a * x * y + y^2 <= 0.
Proof.
  intros a H1. assert (H2 : a <= -2 \/ a >= 2) by nra. destruct H2 as [H2 | H2].
  - exists 1, 1. intros [H3 | H3].
    -- nra.
    -- nra.
  - exists (1), (-1). intros [H3 | H3].
    -- nra.
    -- nra.
Qed.

Lemma lemma_1_18_e : forall x b c,
  c - b^2 / 4 <=  x^2 + b * x + c /\ (x = -b / 2 -> x^2 + b * x + c = c - b^2 / 4).
Proof.
  intros x b c. split.
  - replace (x^2 + b * x + c) with ((x + b / 2)^2 + (c - b^2 / 4)) by nra.
    assert (H1 : (x + b / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
  - intros H1. rewrite H1. nra.
Qed.

Lemma lemma_1_18_e' : forall x a b c,
  a > 0 -> c - b^2 / (4 * a) <= a * x^2 + b * x + c /\ (x = -b / (2 * a) -> a * x^2 + b * x + c = c - b^2 / (4 * a)).
Proof.
  intros x a b c H1. split.
  - replace (a * x^2 + b * x + c) with (a * (x^2 + (b / a) * x + c / a)).
    2 : { replace (a * (x^2 + (b / a) * x + c / a)) with (a * x^2 + a * (b / a * x) + a * (c / a)) by nra. field. nra. }
    assert (H3 : c / a - (b / a)^2 / 4 <= x^2 + (b / a) * x + c / a) by apply lemma_1_18_e.
    apply Rmult_le_compat_r with (r := a) in H3. 2 : { lra. } 
    replace ((c / a - (b / a)^2 / 4) * a) with (c / a * a - ((b / a)^2 / 4) * a) in H3 by nra.
    replace (c / a * a) with c in H3. 2 : { replace (c / a * a) with (a * /a * c) by nra. rewrite Rinv_r. 2 : { lra. } nra. }
    replace ((b / a) ^ 2 / 4 * a) with (b ^ 2 / (4 * a)) in H3 by (field; lra). nra.
  - intro H2. rewrite H2. field; nra.
Qed.

Lemma lemma_1_19_a : forall x1 y1 x2 y2 lam,
  x1 = lam * y1 -> x2 = lam * y2 -> lam >= 0 -> x1 * y1 + x2 * y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 lam H1 H2 H3. assert (H4 : (x1 * y1 + x2 * y2)^2 = (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))^2).
  { rewrite Rpow_mult_distr. repeat rewrite pow2_sqrt. 2 : { nra. } 2 : { nra. } rewrite H1. rewrite H2. nra. }
  apply Rsqr_inj. 2 : { rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply sqrt_pos. } nra.
  repeat rewrite Rsqr_def. nra.
Qed.

Lemma lemma_1_19_a' : forall x1 y1 x2 y2,
  (y1 = 0 /\ y2 = 0) -> x1 * y1 + x2 * y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 [H1 H2]. rewrite H1, H2. replace (x1 * 0 + x2 * 0) with 0 by nra. replace (0^2 + 0^2) with 0 by nra.
  rewrite sqrt_0. nra.
Qed.

Lemma lemma_1_19_a'' : forall x1 y1 x2 y2 lam,
  (y1 <> 0 \/ y2 <> 0) -> lam >= 0 -> ((x1 = lam * y1 /\ x2 = lam * y2) -> False) -> 0 < (lam * y1 - x1)^2 + (lam * y2 - x2)^2.
Proof.
  intros x1 y1 x2 y2 lam [H1 | H1] H2 H3. assert (x1 <> lam * y1 \/ x2 <> lam * y2) as [H4 | H4] by nra.
  - assert (H5 : (lam * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H6 : 0 < (lam * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
    nra.
  - assert (H5 : (lam * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H6 : 0 < (lam * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
    nra.
  - assert (x1 <> lam * y1 \/ x2 <> lam * y2) as [H4 | H4] by nra.
    -- assert (H5 : (lam * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H6 : 0 < (lam * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
    -- assert (H5 : (lam * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H6 : 0 < (lam * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
Qed.

Lemma lemma_1_19_a''' : forall x1 y1 x2 y2,
  y1 <> 0 \/ y2 <> 0 ->
  (forall lam, (x1 <> lam * y1 \/ x2 <> lam * y2)) ->
  x1 * y1 + x2 * y2 < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 H1 H2.
  assert (H3 : forall lam, lam ^ 2 + -2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2) * lam + (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) <> 0).
  {
    intros lam. specialize (H2 lam).
    assert (H3 : 0 < (lam * y1 - x1)^2 + (lam * y2 - x2)^2).
    {
     destruct H2 as [H2 | H2].
     - assert (H3 : (lam * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H4 : 0 < (lam * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
     - assert (H3 : (lam * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H4 : 0 < (lam * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
    }
    replace ((lam * y1 - x1) ^ 2 + (lam * y2 - x2) ^ 2) with (lam^2 * (y1^2 + y2^2) + -2 * lam * (x1 * y1 + x2 * y2) + x1^2 + x2^2) in H3 by nra.
    assert (H4 : lam ^ 2 * (y1 ^ 2 + y2 ^ 2) + -2 * lam * (x1 * y1 + x2 * y2) + x1 ^ 2 + x2 ^ 2 <> 0) by nra.
    assert (H5 : lam^2 + ((-2 * (x1 * y1 + x2 * y2)) / (y1^2 + y2^2)) * lam + (x1^2 + x2^2)/ (y1^2 + y2^2) > 0).
    { 
      apply Rmult_lt_compat_r with (r := 1 / (y1^2 + y2^2)) in H3. 2 : { apply Rdiv_pos_pos. nra. nra. } rewrite Rmult_0_l in H3.
      replace ((lam ^ 2 * (y1 ^ 2 + y2 ^ 2) + -2 * lam * (x1 * y1 + x2 * y2) + x1 ^ 2 + x2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2))) with
              ((lam ^ 2 * (y1 ^ 2 + y2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)) + -2 * lam * (x1 * y1 + x2 * y2) * (1 / (y1 ^ 2 + y2 ^ 2)) + (x1 ^ 2 + x2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)))) in H3 by nra.
      replace ((lam ^ 2 * (y1 ^ 2 + y2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)))) with (lam^2) in H3 by (field; nra).
      replace ((-2 * lam * (x1 * y1 + x2 * y2) * (1 / (y1 ^ 2 + y2 ^ 2)))) with ((-2 * (x1 * y1 + x2 * y2)) / (y1^2 + y2^2) * lam) in H3 by nra. nra.
    }
    assert (H6 : lam ^ 2 + -2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2) * lam + (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) <> 0) by nra.
    nra.
  }
  apply lemma_1_18_a'' in H3. replace ((-2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2)) ^ 2) with ((4 * (x1 * y1 + x2 * y2) ^ 2) / ((y1 ^ 2 + y2 ^ 2) ^ 2)) in H3 by (field; nra).
  assert (H4 : (x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2 - ((x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2)) < 0) by nra.
  assert (H5 : (x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2  < (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2)) by nra.
  assert (H6 : (y1^2 + y2^2 = 0) \/ (y1^2 + y2^2 <> 0)) by lra. destruct H6 as [H6 | H6].
  - nra.
  - assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H20 | H20] by nra.
    { 
      rewrite H20 in H5. rewrite Rdiv_0_l in H5. repeat rewrite <- Rsqr_pow2 in H5. rewrite <- Rsqr_div' in H5. 
      assert (H21 : 0 <= ((x1 * y1 + x2 * y2) / (y1² + y2²))² ) by (apply Rle_0_sqr). nra.
    }
    {
      apply Rmult_lt_compat_r with (r := (y1 ^ 2 + y2 ^ 2) ^ 2) in H5. 2 : { nra. }
      assert (0 < sqrt (y1 ^ 2 + y2 ^ 2)) as H7. { apply sqrt_lt_R0. nra. }
      replace ((x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2 * (y1 ^ 2 + y2 ^ 2) ^ 2) with ((x1 * y1 + x2 * y2) ^ 2) in H5 by (field; nra).
      replace ((x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) * (y1 ^ 2 + y2 ^ 2) ^ 2) with ((x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2)) in H5 by (field; nra).
      apply sqrt_lt_1 in H5. 2 : { rewrite <- Rsqr_pow2. apply Rle_0_sqr. } 2 : { nra. }
      pose proof Rtotal_order (x1 * y1 + x2 * y2) 0 as [H8 | [H8 | H8]].
      2 : {
          assert (H9 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H9 as [H9 | H9].
          - rewrite H9 in H5. rewrite H8 in H4. replace (0^2) with 0 in H5 by nra. rewrite Rmult_0_l in H5. rewrite sqrt_0 in H5.
            assert (H10 : 0 <= sqrt ((x1 * y1 + x2 * y2)^2)) by (apply sqrt_pos). nra.
          - rewrite H8. rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply sqrt_lt_R0. nra.
      }
      2 : {
        assert (H9 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H9 as [H9 | H9].
        - rewrite H9 in H5. rewrite Rmult_0_l in H5. rewrite sqrt_0 in H5.
          assert (H10 : 0 <= sqrt ((x1 * y1 + x2 * y2)^2)) by (apply sqrt_pos). nra.
        - rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } rewrite sqrt_pow2 in H5. 2 : { nra. } nra.
      }
      rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } 
      assert (H9 : 0 <= sqrt ((x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2))) by (apply sqrt_pos). nra.
    }
Qed.

Lemma lemma_1_19_b : forall x y x1 y1 x2 y2,
  x = x1 / (sqrt (x1^2 + x2^2)) -> y = y1 / (sqrt (y1^2 + y2^2)) -> x = x2 / (sqrt (x1^2 + x2^2)) -> 
  y = y2 / (sqrt (y1^2 + y2^2))-> x1 * y1 + x2 * y2 <= sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2).
Proof.
  intros x y x1 y1 x2 y2 H1 H2 H3 H4.
  assert (H5 : 0 <= x^2 - 2*x*y + y^2).
  { replace (x^2 - 2*x*y + y^2) with ((x - y)^2) by field. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (2*x*y <= x^2 + y^2) as H6 by nra. pose proof H6 as H7.
  rewrite H1 in H6. rewrite H2 in H6. rewrite H3 in H7. rewrite H4 in H7. 
  replace ((x1 / sqrt (x1 ^ 2 + x2 ^ 2)) ^ 2) with
          ((x1 ^ 2 / (sqrt (x1 ^ 2 + x2 ^ 2)^2))) in H6.
          2 : { assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H8 | H9] by lra. 
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < sqrt (x1 ^ 2 + x2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H6. 2 : { nra. }
  replace ((y1 / sqrt (y1 ^ 2 + y2 ^ 2)) ^ 2) with
          ((y1 ^ 2 / (sqrt (y1 ^ 2 + y2 ^ 2)^2))) in H6.
          2 : { assert (y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) as [H8 | H9] by lra. 
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < sqrt (y1 ^ 2 + y2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H6. 2 : { nra. }
  replace ((x2 / sqrt (x1 ^ 2 + x2 ^ 2)) ^ 2) with
          ((x2 ^ 2 / (sqrt (x1 ^ 2 + x2 ^ 2)^2))) in H7.
          2 : { assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H8 | H9] by lra. 
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < sqrt (x1 ^ 2 + x2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H7. 2 : { nra. }
  replace ((y2 / sqrt (y1 ^ 2 + y2 ^ 2)) ^ 2) with
          ((y2 ^ 2 / (sqrt (y1 ^ 2 + y2 ^ 2)^2))) in H7.
          2 : { assert (y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) as [H8 | H9] by lra. 
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < sqrt (y1 ^ 2 + y2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H7. 2 : { nra. }
  replace (2 * (x1 / sqrt (x1 ^ 2 + x2 ^ 2)) * (y1 / sqrt (y1 ^ 2 + y2 ^ 2))) with 
          ((2 * x1 * y1) / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) in H6.
          2 : 
          {
            assert ((sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) = 0 \/ (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) <> 0) as [H8 | H9] by lra.
            - rewrite H8. unfold Rdiv. rewrite Rinv_0. rewrite Rmult_0_r. assert (H9 : sqrt (x1 ^ 2 + x2 ^ 2) = 0 \/ sqrt (y1 ^ 2 + y2 ^ 2) = 0) by nra.
              destruct H9 as [H9 | H9].
              -- rewrite H9. rewrite Rinv_0. nra.
              -- rewrite H9. rewrite Rinv_0. nra.
            - field. nra.
          }
  replace (2 * (x2 / sqrt (x1 ^ 2 + x2 ^ 2)) * (y2 / sqrt (y1 ^ 2 + y2 ^ 2))) with 
          ((2 * x2 * y2) / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) in H7.
          2 : 
          {
            assert ((sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) = 0 \/ (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) <> 0) as [H8 | H9] by lra.
            - rewrite H8. unfold Rdiv. rewrite Rinv_0. rewrite Rmult_0_r. assert (H9 : sqrt (x1 ^ 2 + x2 ^ 2) = 0 \/ sqrt (y1 ^ 2 + y2 ^ 2) = 0) by nra.
              destruct H9 as [H9 | H9].
              -- rewrite H9. rewrite Rinv_0. nra.
              -- rewrite H9. rewrite Rinv_0. nra.
            - field. nra.
          }
  assert (H8 : 2 * x1 * y1 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) + 2 * x2 * y2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) <= 
              x1 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y1 ^ 2 / (y1 ^ 2 + y2 ^ 2) + x2 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y2 ^ 2 / (y1 ^ 2 + y2 ^ 2)) by nra.
  replace (2 * x1 * y1 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) + 2 * x2 * y2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with 
          ( (2 * x1 * y1 + 2 * x2 * y2) / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) in H8 by nra.
  assert ((x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0) /\ (y1^2 + y2^2 = 0) \/ (y1^2 + y2^2 <> 0)) as [H9 | H10] by lra.
  - assert (x1 = 0 /\ x2 = 0) as [H10 H11] by nra. rewrite H10, H11. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
  - destruct H10 as [[H10 H11] | H10].
    -- assert (y1 = 0 /\ y2 = 0) as [H12 H13] by nra. rewrite H12, H13. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
    -- assert (H11 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H11 as [H11 | H11].
       --- assert (x1 = 0 /\ x2 = 0) as [H12 H13] by nra. rewrite H12, H13. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
       --- replace (x1 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y1 ^ 2 / (y1 ^ 2 + y2 ^ 2) + x2 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y2 ^ 2 / (y1 ^ 2 + y2 ^ 2)) with
           2 in H8 by (field; nra). assert (H12 : sqrt (x1 ^ 2 + x2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
           assert (H13 : sqrt (y1 ^ 2 + y2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
           apply Rmult_le_compat_r with (r := (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) in H8. 2 : { nra. }
           replace ((2 * x1 * y1 + 2 * x2 * y2) / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) * (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with
                   (2 * x1 * y1 + 2 * x2 * y2) in H8 by (field; nra). nra.
Qed.

Lemma lemma_1_19_c : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 <= sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2. assert (H1 : (x1^2 + x2^2) * (y1^2 + y2^2) = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2) by nra.
  assert (H2 : (x1*y2 - x2*y1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : (x1 * y1 + x2 * y2) ^ 2 <= (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2)) by nra.
  assert (H4 : (x1 * y1 + x2 * y2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  apply sqrt_le_1 in H3. 2 : { nra. } 2 : { nra. } 
  pose proof Rtotal_order (x1 * y1 + x2 * y2) 0 as [H5 | [H5 | H5]].
  2 : { 
        rewrite H5. assert (H6 : 0 <= sqrt (x1^2 + x2^2)). { apply sqrt_positivity. nra. } 
        assert (H7 : 0 <= sqrt (y1^2 + y2^2)). { apply sqrt_positivity. nra. } nra. 
      }
  2 : { rewrite sqrt_pow2 in H3. 2 : { nra. } rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply H3. }
  assert (H6 : sqrt (x1^2 + x2^2) > 0). { apply sqrt_lt_R0. nra. } assert (H7 : sqrt (y1^2 + y2^2) > 0). { apply sqrt_lt_R0. nra. }
  nra.
Qed.

Lemma contra_3 : forall P Q R,
  (P -> Q -> R) -> (~R -> ~P \/ ~Q).
Proof.
  intros P Q R H1. tauto.
Qed.

Lemma lemma_1_19_d_a : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) ->
  (y1 = 0 /\ y2 = 0) \/ exists lam, x1 = lam * y1 /\ x2 = lam * y2.
Proof.
  intros x1 y1 x2 y2 H1.
  pose proof contra_3 (y1 <> 0 \/ y2 <> 0) (forall lam, (x1 <> lam * y1 \/ x2 <> lam * y2)) (x1 * y1 + x2 * y2 < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) as H2.
  pose proof lemma_1_19_a''' x1 y1 x2 y2 as H3. apply H2 in H3.
  - destruct H3 as [H3 | H3].
    + left. nra.
    + right. apply not_all_ex_not in H3. destruct H3 as [lam H3]. apply not_or_and in H3. destruct H3 as [H3 H4].
      exists lam. nra.
  - apply Rle_not_lt. apply Req_le. apply sym_eq. apply H1.
Qed.  

Lemma lemma_1_19_d_b : forall x y x1 y1 x2 y2,
  x = x1 / (sqrt (x1^2 + x2^2)) -> y = y1 / (sqrt (y1^2 + y2^2)) -> x = x2 / (sqrt (x1^2 + x2^2)) -> 
  y = y2 / (sqrt (y1^2 + y2^2))-> x1 * y1 + x2 * y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) ->
  (y1 = 0 /\ y2 = 0) \/ exists lam, x1 = lam * y1 /\ x2 = lam * y2.
Proof.
  intros x y x1 y1 x2 y2 H1 H2 H3 H4 H5.
  assert (H6 : x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) by lra. destruct H6 as [H6 | H6].
  - assert (H7 : y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) by lra. destruct H7 as [H7 | H7].
    + left. nra.
    + right. assert (H8 : x1 = 0 /\ x2 = 0) by nra. exists 0. nra.
  - assert (H7 : y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) by nra. destruct H7 as [H7 | H7].
    + left. nra.
    + assert (H8 : 0 < sqrt (x1^2 + x2^2)). { apply sqrt_lt_R0. nra. }
      assert (H9 : 0 < sqrt (y1^2 + y2^2)). { apply sqrt_lt_R0. nra. }
      right. exists (sqrt (x1^2 + x2^2) / sqrt (y1^2 + y2^2)). split.
      * assert (H10 : x1 * y1 + x2 * y2 = 0 \/ x1 * y1 + x2 * y2 <> 0) by lra. destruct H10 as [H10 | H10].
        -- nra.
        -- apply Rmult_eq_compat_l with (r := 2 / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))) in H5.
           replace (2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) * (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with
                   2 in H5 by (field; nra). replace 2 with (x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2) + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)) in H5 at 2 by (field; nra).
           replace (2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) * (x1 * y1 + x2 * y2)) with 
                   ((2*x1*y1 / (sqrt (x1^2 + x2^2) * sqrt(y1^2 + y2^2))) + (2*x2*y2 / (sqrt (x1^2 + x2^2) * sqrt(y1^2 + y2^2)))) in H5 by (field; nra).
           replace (2 * x1 * y1 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H1. rewrite H2. field. nra. }
           replace (2 * x2 * y2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H3. rewrite H4. field. nra. }
           assert (H11 : 4 * x * y = 2 * (x^2 + y^2)).
           {
              replace (2 * x * y + 2 * x * y) with (4 * x * y) in H5 by nra. simpl. repeat rewrite Rmult_1_r.
              replace (2 * (x * x + y * y)) with (x * x + y * y + x * x + y * y) by nra.
              rewrite H1 at 2 3. replace (x1 / sqrt (x1 ^ 2 + x2 ^ 2) * (x1 / sqrt (x1 ^ 2 + x2 ^ 2))) with
                      (x1^2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H2 at 2 3. replace (y1 / sqrt (y1 ^ 2 + y2 ^ 2) * (y1 / sqrt (y1 ^ 2 + y2 ^ 2))) with
                      (y1^2 / (sqrt (y1 ^ 2 + y2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H3 at 2 3. replace (x2 / sqrt (x1 ^ 2 + x2 ^ 2) * (x2 / sqrt (x1 ^ 2 + x2 ^ 2))) with
                      (x2^2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H4 at 2 3. replace (y2 / sqrt (y1 ^ 2 + y2 ^ 2) * (y2 / sqrt (y1 ^ 2 + y2 ^ 2))) with
                      (y2^2 / (sqrt (y1 ^ 2 + y2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              nra.
           }
           assert (H12 : x = y) by nra.
           assert (x1 = 0 \/ x1 <> 0) as [H13 | H13] by nra.
           { 
             rewrite H13 in H1. rewrite Rdiv_0_l in H1. rewrite H1 in H3. apply Rmult_eq_compat_r with (r := sqrt (x1^2 + x2^2)) in H3.
             replace (x2 / sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2)) with (x2 * (sqrt (x1 ^ 2 + x2 ^ 2) / sqrt (x1 ^ 2 + x2 ^ 2))) in H3 by nra.
             rewrite Rdiv_diag in H3. nra. nra.
           }
           {
             replace x1 with (x * sqrt (x1 ^ 2 + x2 ^ 2)) at 1. 2 : { rewrite H1. field. nra. }
             replace y1 with (y * sqrt (y1 ^ 2 + y2 ^ 2)) at 2. 2 : { rewrite H2. field. nra. }
             replace (sqrt (x1 ^ 2 + x2 ^ 2) / sqrt (y1 ^ 2 + y2 ^ 2) * (y * sqrt (y1 ^ 2 + y2 ^ 2))) with 
                      (y * sqrt(x1^2 + x2^2)) by (field; nra).
             apply Rmult_eq_reg_r with (r := / sqrt (x1^2 + x2^2)). 2 : { apply Rinv_neq_0_compat. nra. }
             replace (x * sqrt (x1 ^ 2 + x2 ^ 2) * / sqrt (x1 ^ 2 + x2 ^ 2)) with x by (field; nra).
             replace (y * sqrt (x1 ^ 2 + x2 ^ 2) * / sqrt (x1 ^ 2 + x2 ^ 2)) with y by (field; nra).
             apply H12.
           }
      * assert (H10 : x1 * y1 + x2 * y2 = 0 \/ x1 * y1 + x2 * y2 <> 0) by lra. destruct H10 as [H10 | H10].
        -- nra.
        -- apply Rmult_eq_compat_l with (r := 2 / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))) in H5.
           replace (2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) * (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with
                   2 in H5 by (field; nra). replace 2 with (x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2) + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)) in H5 at 2 by (field; nra).
           replace (2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2)) * (x1 * y1 + x2 * y2)) with 
                   ((2*x1*y1 / (sqrt (x1^2 + x2^2) * sqrt(y1^2 + y2^2))) + (2*x2*y2 / (sqrt (x1^2 + x2^2) * sqrt(y1^2 + y2^2)))) in H5 by (field; nra).
           replace (2 * x1 * y1 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H1. rewrite H2. field. nra. }
           replace (2 * x2 * y2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H3. rewrite H4. field. nra. }
           assert (H11 : 4 * x * y = 2 * (x^2 + y^2)).
           {
              replace (2 * x * y + 2 * x * y) with (4 * x * y) in H5 by nra. simpl. repeat rewrite Rmult_1_r.
              replace (2 * (x * x + y * y)) with (x * x + y * y + x * x + y * y) by nra.
              rewrite H1 at 2 3. replace (x1 / sqrt (x1 ^ 2 + x2 ^ 2) * (x1 / sqrt (x1 ^ 2 + x2 ^ 2))) with
                      (x1^2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H2 at 2 3. replace (y1 / sqrt (y1 ^ 2 + y2 ^ 2) * (y1 / sqrt (y1 ^ 2 + y2 ^ 2))) with
                      (y1^2 / (sqrt (y1 ^ 2 + y2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H3 at 2 3. replace (x2 / sqrt (x1 ^ 2 + x2 ^ 2) * (x2 / sqrt (x1 ^ 2 + x2 ^ 2))) with
                      (x2^2 / (sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H4 at 2 3. replace (y2 / sqrt (y1 ^ 2 + y2 ^ 2) * (y2 / sqrt (y1 ^ 2 + y2 ^ 2))) with
                      (y2^2 / (sqrt (y1 ^ 2 + y2 ^ 2) * sqrt (y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              nra.
           }
           assert (H12 : x = y) by nra.
           assert (x2 = 0 \/ x2 <> 0) as [H13 | H13] by nra.
           { 
             rewrite H13 in H3. rewrite Rdiv_0_l in H3. rewrite H3 in H1. apply Rmult_eq_compat_r with (r := sqrt (x1^2 + x2^2)) in H1.
             replace (x1 / sqrt (x1 ^ 2 + x2 ^ 2) * sqrt (x1 ^ 2 + x2 ^ 2)) with (x1 * (sqrt (x1 ^ 2 + x2 ^ 2) / sqrt (x1 ^ 2 + x2 ^ 2))) in H1 by nra.
             rewrite Rdiv_diag in H1. nra. nra.
           }
           {
             replace x2 with (x * sqrt (x1 ^ 2 + x2 ^ 2)) at 1. 2 : { rewrite H3. field. nra. }
             replace y2 with (y * sqrt (y1 ^ 2 + y2 ^ 2)) at 2. 2 : { rewrite H4. field. nra. }
             replace (sqrt (x1 ^ 2 + x2 ^ 2) / sqrt (y1 ^ 2 + y2 ^ 2) * (y * sqrt (y1 ^ 2 + y2 ^ 2))) with 
                      (y * sqrt(x1^2 + x2^2)) by (field; nra).
             apply Rmult_eq_reg_r with (r := / sqrt (x1^2 + x2^2)). 2 : { apply Rinv_neq_0_compat. nra. }
             replace (x * sqrt (x1 ^ 2 + x2 ^ 2) * / sqrt (x1 ^ 2 + x2 ^ 2)) with x by (field; nra).
             replace (y * sqrt (x1 ^ 2 + x2 ^ 2) * / sqrt (x1 ^ 2 + x2 ^ 2)) with y by (field; nra).
             apply H12.
           }
Qed.

Lemma lemma_1_19_d_c : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) -> ((y1 = 0 /\ y2 = 0) \/ exists lam, x1 = lam * y1 /\ x2 = lam * y2).
Proof.
  intros x1 y1 x2 y2 H1. assert (H2 : (x1^2 + x2^2) * (y1^2 + y2^2) = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2) by nra.
  assert (H3 : x1 * y2 - x2 * y1 = 0 \/ x1 * y2 - x2 * y1 <> 0) by lra. destruct H3 as [H3 | H3].
  - rewrite H3 in H2. replace (0^2) with 0 in H2 by nra. rewrite Rplus_0_r in H2.
    assert (H4 : x1 * y2 = x2 * y1) by nra. assert (H5 : (y1 = 0 /\ y2 = 0) \/ (y1 = 0 /\ y2 <> 0) \/ (y1 <> 0 /\ y2 = 0) \/ (y1 <> 0 /\ y2 <> 0)) by lra.
    destruct H5 as [[H5 H6] | [[H5 H6] | [[H5 H6] | [H5 H6]]]].
    -- left. nra.
    -- right. exists (x2 / y2). split.
       --- replace (x2 / y2 * y1) with ((x2 * y1) / y2) by (field; nra). rewrite <- H4. field. nra.
       --- replace (x2 / y2 * y2) with ((x2 * y2) / y2) by (field; nra). field. nra.
    -- right. assert (H7 : x2 = 0) by nra. exists (x1 / y1). split.
       --- replace (x1 / y1 * y1) with ((x1 * y1) / y1) by (field; nra). field. nra.
       --- rewrite H7. rewrite H6. nra.
    -- right. exists (x1 / y1). split.
       --- replace (x1 / y1 * y1) with ((x1 * y1) / y1) by (field; nra). field. nra.
       --- replace (x1 / y1 * y2) with ((x1 * y2) / y1) by (field; nra). rewrite H4. field. nra.
- assert (H4 : x1 <> 0 \/ x2 <> 0) by nra. assert (H5 : y1 <> 0 \/ y2 <> 0) by nra.
  assert (H6 : x1^2 + x2^2 > 0) by nra. assert (H7 : y1^2 + y2^2 > 0) by nra. rewrite <- sqrt_mult in H1. 2 : { nra. } 2 : { nra. }
  assert (H8 : sqrt (x1 ^ 2 + x2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
  assert (H9 : (x1*y1 + x2*y2)^2 = sqrt (x1^2 + x2^2)^2 * sqrt (y1^2 + y2^2)^2).  
  { rewrite H1. rewrite pow2_sqrt. 2 : { nra. } rewrite pow2_sqrt. 2 : { nra. } rewrite pow2_sqrt. 2 : { nra. } reflexivity. }
  rewrite pow2_sqrt in H9. 2 : { nra. } rewrite pow2_sqrt in H9. 2 : { nra. } nra.
Qed.

Lemma lemma_1_20 : forall x x0 y y0 eps,
  Rabs (x - x0) < eps / 2 -> Rabs (y - y0) < eps / 2 -> (Rabs ((x + y) - (x0 + y0)) < eps /\ Rabs ((x - y) - (x0 - y0)) < eps).
Proof.
  solve_abs.
Qed.

Lemma Rdiv_lt_1: forall a b : R, a < b -> b > 0 -> a / b < 1.
Proof.
  intros a b H1 H2.
  apply Rmult_lt_compat_r with (r := 1/b) in H1.
  - replace (a * (1 / b)) with (a / b) in H1 by lra.
    replace (b * (1 / b)) with 1 in H1 by (field; lra).
    apply H1.
  - apply Rdiv_pos_pos. lra. apply H2.
Qed.  

Lemma lemma_1_21 : forall x x0 y y0 eps,
  Rabs (x - x0) < Rmin (eps / (2 * (Rabs (y0) + 1))) 1 -> Rabs (y - y0) < eps / (2 * ((Rabs x0) + 1)) -> Rabs (x * y - x0 * y0) < eps.
Proof.
  intros x x0 y y0 eps H1 H2. assert (H3 : (Rabs (x - x0)) < 1). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H4 : Rabs x - Rabs x0 < 1). { pose proof lemma_1_12_v x x0. lra. }
  assert (H5 : Rabs (y - y0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H6 : Rabs x0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H7 : eps > 0).
  { 
    pose proof Rtotal_order eps 0 as [H7 | [H7 | H7]].
    - assert (H8 : eps / (2 * (Rabs x0 + 1)) < 0). { apply Rdiv_neg_pos. lra. lra. } lra.
    - nra.
    - apply H7.
  }
  assert (H8 : Rabs x < 1 + Rabs x0) by lra. replace (x * y - x0 * y0) with (x * (y - y0) + y0 * (x - x0)) by lra.
  assert (H9 : Rabs (x * (y - y0) + y0 * (x - x0)) <= Rabs x * Rabs (y - y0) + Rabs y0 * Rabs (x - x0)). 
  { repeat rewrite <- lemma_1_12_i. apply Rabs_triang. }
  assert (H10 : (1 + Rabs x0) * (eps / (2 * (Rabs x0 + 1))) = eps / 2). { field; try unfold Rabs; try destruct Rcase_abs; try nra. }

  assert (H : forall x, x >= 0 -> x / (2 * (x + 1)) < 1 / 2).
  {
    intros x1 H11. apply Rmult_lt_reg_l with (r := 2). lra. unfold Rdiv.
  replace (2 * (1 * / 2)) with (1) by lra. replace (2 * (x1 * / (2 * (x1 + 1)))) with ((x1) * (2 * / (2 * (x1 + 1)))) by lra.
  rewrite Rinv_mult. replace (2 * (/ 2 * / (x1 + 1))) with (2 * / 2 * / (x1 + 1)) by nra. rewrite Rinv_r. 2 : lra.
  rewrite Rmult_1_l. rewrite <- Rdiv_def. apply Rdiv_lt_1. lra. lra.
  }
  assert (H11 : (Rabs y0 * (eps / (2 * ((Rabs y0) + 1)))) < eps / 2). 
  { 
    replace (Rabs y0 * (eps / (2 * (Rabs y0 + 1)))) with (eps * (Rabs y0 * / (2 * (Rabs y0 + 1)))) by lra.
    pose proof H (Rabs y0) as H12. unfold Rdiv. apply Rmult_lt_compat_l. lra. unfold Rdiv in H12. rewrite Rmult_1_l in H12.
    apply H12. apply Rle_ge. apply Rabs_pos.
  }
  replace (eps) with (eps / 2 + eps / 2) by lra. 
  assert (H12 : Rabs x * Rabs (y - y0) < ((1 + Rabs x0) * (eps / (2 * (Rabs x0 + 1))))) by nra.
  assert (H13 : Rabs (x - x0) < (eps / (2 * (Rabs y0 + 1)))). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H14 : Rabs y0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H15 : Rabs (x - x0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H16 : Rabs y0 * Rabs (x - x0) <= (Rabs y0 * (eps / (2 * ((Rabs y0 + 1)))))) by nra.
  nra.
Qed.

Lemma lemma_1_22 : forall y y0 eps,
  (y0 <> 0) -> (Rabs (y - y0) < Rmin (Rabs (y0 / 2)) ((eps * (Rabs y0)^2) / 2)) -> (y <> 0 /\ Rabs (1 / y - 1 / y0) < eps).
Proof.
  intros y y0 eps H1 H2. assert (H3 : y <> 0).
  - assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H5 : Rabs (y - y0) < (eps * (Rabs y0)^2) / 2). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H6 : Rabs y > Rabs y0 / 2) by solve_abs.
       assert (H7 : Rabs y > 0) by solve_abs. assert (H8 : Rabs y0 > 0) by solve_abs.
       assert (H9 : forall a b : R, a > 0 -> b > 0 -> a > b / 2 -> 1 / a < 2 / b).
       { 
          intros a b H9 H10 H11. apply Rmult_lt_reg_r with (r := a). lra. replace (1 / a * a) with 1 by (field; lra).
          apply Rmult_lt_reg_r with (r := b). lra. replace (2 / b * a * b) with (2 * a) by (field; lra). lra.
       }
       assert (H10 : 1 / Rabs y < 2 / Rabs y0). { apply H9. apply H7. apply H8. apply H6. } clear H9.
       replace (1 / y - 1 / y0) with ((y0 - y) / (y * y0)) by (field; lra). 
       unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite <- Rdiv_def. rewrite Rabs_mult.
       rewrite Rabs_minus_sym. assert (H11 : 2 * Rabs (y - y0) < eps * Rabs y0 ^ 2). { lra. }
       assert (H12 : (2 * Rabs (y - y0)) / (Rabs y0 ^ 2) < eps).
       { apply Rmult_lt_reg_r with (r := Rabs y0 ^ 2). nra. apply Rmult_lt_reg_r with (r := / 2). nra.
          replace (2 * Rabs (y - y0) / (Rabs y0 ^ 2) * Rabs y0 ^2 * / 2) with 
          (2 * Rabs (y - y0) * / 2) by (field; lra). lra.
       }
       replace (2 * Rabs (y - y0) / Rabs y0 ^ 2) with (Rabs (y - y0) / ((Rabs y0 / 2) * Rabs y0)) in H12 by (field; nra).
       assert (H13 : (Rabs y0 / 2 * Rabs y0) < Rabs y * Rabs y0) by nra. 
       assert (H14 : forall a b c, a > 0 -> b > 0 -> c >= 0 -> a > b -> c / a <= c / b).
       {
          intros a b c H14 H15 H16 H17. apply Rmult_le_reg_r with (r := a). lra.
          replace (c / a * a) with c by (field; lra). apply Rmult_le_reg_r with (r := b). lra.
          replace (c / b * a * b) with (c * a) by (field; lra). nra.
       }
       assert (H15 : Rabs (y - y0) / (Rabs y0 / 2 * Rabs y0) >= Rabs (y - y0) / (Rabs y * Rabs y0)). 
       { apply Rle_ge. apply H14. nra. nra. apply Rle_ge. apply Rabs_pos. nra. }
       nra.
Qed. 

Lemma lemma_1_23 : forall x y x0 y0 eps,
  (y0 <> 0) -> (Rabs (x - x0) < Rmin (eps / (2 * (1 / Rabs y0 + 1))) 1) -> (Rabs (y - y0) < Rmin (Rabs (y0 / 2)) ((eps * (Rabs y0)^2) / (4 * ((Rabs x0) + 1)))) -> (y <> 0 /\ Rabs (x / y - x0 / y0) < eps).
Proof.
  intros x y x0 y0 eps H1 H2 H3. 
  assert (H4 : 4 * ((Rabs x0) + 1) > 2) by solve_abs.
  assert (H5 : eps >= 0).
  { 
    pose proof Rtotal_order eps 0 as [H5 | [H5 | H5]].
    - assert (H6 : eps / (2 * (1 / Rabs y0 + 1)) < 0). 
      {
         apply Rdiv_neg_pos. nra.
         assert (1 / Rabs y0 >= 0). 
         {
            assert (Rabs y0 = 0 \/ Rabs y0 > 0) as [H7 | H7] by solve_abs.
            - rewrite H7. unfold Rdiv. rewrite Rmult_1_l. rewrite Rinv_0. nra.
            - unfold Rdiv. rewrite Rmult_1_l. apply Rgt_ge. apply Rinv_0_lt_compat. apply H7.
         } 
         nra.
      }
      assert (H7 : Rabs (x - x0) >= 0) by solve_abs. apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra.
    - nra.
    - nra.
  }
  split.
  - assert (H6 : forall a b c : R, a >= 0 -> b > 0 -> c > 0 -> b >= c -> a / b <= a / c).
    { intros a b c H6 H7 H8 H9. apply Rmult_le_reg_r with (r := b). nra.
      replace (a / b * b) with a by (field; lra). apply Rmult_le_reg_r with (r := c). lra.
      replace (a / c * b * c) with (a * b) by (field; lra). nra.
    }
    assert (H7 : eps * Rabs y0 ^ 2 / (4 * (Rabs x0 + 1)) <= eps * Rabs y0 ^ 2 / 2).
    { apply H6. nra. nra. nra. nra. }
    assert (H8 : Rabs (y - y0) < eps * Rabs y0 ^ 2 / (4 * (Rabs x0 + 1))).
    { apply Rlt_gt in H3. apply Rmin_Rgt_l in H3. lra. } 
    assert (H9 : Rabs (y - y0) < Rabs (y0 / 2)).
    { apply Rlt_gt in H3. apply Rmin_Rgt_l in H3. lra. }
    apply lemma_1_22 with (y0 := y0) (eps := eps). 2 : { apply Rmin_glb_lt. nra. nra. } nra.
  - assert (H6 : 1 / Rabs y0 = Rabs (/ y0)). { unfold Rdiv. rewrite Rmult_1_l. rewrite Rabs_inv. reflexivity. }
    unfold Rdiv. apply lemma_1_21.
    -- rewrite H6 in H2. apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. apply Rmin_glb_lt. nra. nra.
    -- repeat rewrite <- Rdiv_1_l. apply lemma_1_22. nra. 
       replace (eps / (2 * (Rabs x0 + 1)) * Rabs y0 ^ 2 / 2) with (eps * Rabs y0 ^ 2 / (4 * (Rabs x0 + 1))) by (field; nra).
       nra.
Qed.

(* 1 2 3 4  - > 1 + (2 + (3 + 4)) *)

Fixpoint standard_sum (l : list R) : R :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => x + standard_sum xs
  end.

(* 1 2 3 4 *)
(* 1 | 2 3 4 -> 1 + (2 + (3 + 4)), 1 + ((2 + 3) + 4)*)
(* 1 2 | 3 4 -> (1 + 2) + (3 + 4)*)
(* 1 2 3 | 4 -> (1 + (2 + 3)) + 4, ((1 + 2) + 3) + 4 *)

Inductive add_expr : Type :=
| Num (a : R)
| Sum (e1 e2 : add_expr).

Fixpoint eval_add_expr (e : add_expr) : R :=
  match e with
  | Num a => a
  | Sum e1 e2 => (eval_add_expr e1) + (eval_add_expr e2)
  end.

Fixpoint elements (e : add_expr) : list R :=
  match e with
  | Num a => [a]
  | Sum e1 e2 => elements e1 ++ elements e2
  end.

Lemma lemma_1_24_a : forall (l : list R) (a : R),
  standard_sum l + a  = standard_sum (l ++ [a]).
Proof.
  intros l a. induction l as [| a' l' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. destruct l' as [| a'' l''] eqn:El.
    -- simpl. lra.
    -- simpl. lra.
Qed.

Lemma lemma_1_24_b : forall l1 l2,
  standard_sum (l1 ++ l2) = standard_sum l1 + standard_sum l2.
Proof.
  intros l1 l2. generalize dependent l1.
  induction l2 as [| a l2' IH].
  - intros l1. rewrite app_nil_r. simpl. lra.
  - intros l1. replace (standard_sum (a :: l2')) with (a + standard_sum l2'). 
    2 : { simpl. destruct l2'. simpl. lra. reflexivity. } 
    rewrite Rplus_comm. rewrite Rplus_assoc.
    replace (l1 ++ a :: l2') with ((l1 ++ [a]) ++ l2') by (rewrite <- app_assoc; reflexivity).
    specialize IH with (l1 ++ [a]).
    rewrite IH. rewrite <- lemma_1_24_a. lra.
Qed.

Set Printing Parentheses.

Example eval_add_expr_1234_1 : eval_add_expr (Sum (Num 1) (Sum (Num 2) (Sum (Num 3) (Num 4)))) = 10.
Proof.
  simpl. lra.
Qed.

Example eval_add_expr_1234_2 : eval_add_expr (Sum (Num 1) (Sum (Sum (Num 2) (Num 3)) (Num 4))) = 10.
Proof.
  simpl. lra.
Qed.

Example eval_add_expr_1234_3 : eval_add_expr (Sum (Sum (Num 1) (Num 2)) (Sum (Num 3) (Num 4))) = 10.
Proof.
  simpl. lra.
Qed.

Example eval_add_expr_1234_4 : eval_add_expr (Sum (Sum (Num 1) (Sum (Num 2) (Num 3))) (Num 4)) = 10.
Proof.
  simpl. lra.
Qed.

Example eval_add_expr_1234_5 : eval_add_expr (Sum (Sum (Sum (Num 1) (Num 2)) (Num 3)) (Num 4)) = 10.
Proof.
  simpl. lra.
Qed.

Unset Printing Parentheses.

Example elements_add_expr_1234_1 : 
  elements (Sum (Num 1) (Sum (Num 2) (Sum (Num 3) (Num 4)))) = [1;2;3;4].
Proof.
  simpl. reflexivity.
Qed.

Example elements_add_expr_1234_2 : 
  elements (Sum (Num 1) (Sum (Sum (Num 2) (Num 3)) (Num 4))) = [1;2;3;4].
Proof.
  simpl. reflexivity.
Qed.

Example elements_add_expr_1234_3 : 
  elements (Sum (Sum (Num 1) (Num 2)) (Sum (Num 3) (Num 4))) = [1;2;3;4].
Proof.
  simpl. reflexivity.
Qed.

Example elements_add_expr_1234_4 : 
  elements (Sum (Sum (Num 1) (Sum (Num 2) (Num 3))) (Num 4)) = [1;2;3;4].
Proof.
  simpl. reflexivity.
Qed.

Example elements_add_expr_1234_5 : 
  elements (Sum (Sum (Sum (Num 1) (Num 2)) (Num 3)) (Num 4)) = [1;2;3;4].
Proof.
  simpl. reflexivity.
Qed.

Lemma lemma_1_24_c : forall (e : add_expr),
  eval_add_expr e = standard_sum (elements e).
Proof.
  intros e. induction e as [a | e1 IH1 e2 IH2].
  - simpl. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. rewrite lemma_1_24_b. reflexivity.
Qed.

Lemma addition_assoc_R : forall e1 e2 : add_expr,
  elements e1 = elements e2 -> eval_add_expr e1 = eval_add_expr e2.
Proof.
  intros e1 e2 H. repeat rewrite lemma_1_24_c. rewrite H. reflexivity.
Qed.

Module module_1_25.

Inductive number : Type :=
  | zero
  | one.

Definition plus' (a b : number) : number :=
  match a, b with
  | zero, zero => zero
  | one, one => zero
  | _, _ => one
  end.

Definition mult' (a b : number) : number :=
  match a, b with
  | one, one => one
  | _, _ => zero
  end.

Notation "x + y" := (plus' x y).
Notation "x * y" := (mult' x y).

Lemma lemma_1_25_P1 : forall a b c : number,
  a + (b + c) = (a + b) + c.
Proof.
  destruct a, b, c; reflexivity.
Qed.

Lemma lemma_1_25_P2 : forall a : number, 
  exists i : number, a + i = a.
Proof.
  intros a. exists zero. destruct a; reflexivity.
Qed.

Lemma lemma_1_25_P3 : forall a : number,
  exists i : number, a + i = zero.
Proof.
  intros a. destruct a.
  - exists zero. reflexivity.
  - exists one. reflexivity.
Qed.

Lemma lemma_1_25_P4 : forall a b : number,
  a + b = b + a.
Proof.
  intros a b. destruct a, b; reflexivity.
Qed.

Lemma lemma_1_25_P6 : forall a : number,
  exists i : number, a * i = a.
Proof.
  intros a. exists one. destruct a; reflexivity.
Qed.

Lemma lemma_1_25_P7 : forall a : number,
  exists i : number, a * i = zero.
Proof.
  intros a. destruct a.
  - exists one. reflexivity.
  - exists zero. reflexivity.
Qed.

Lemma lemma_1_25_P8 : forall a b : number,
  a * b = b * a.
Proof.
  intros a b. destruct a, b; reflexivity.
Qed.

Lemma lemma_1_25_P9 : forall a b c : number,
  a * (b + c) = a * b + a * c.
Proof.
  destruct a, b, c; reflexivity.
Qed.

End module_1_25.