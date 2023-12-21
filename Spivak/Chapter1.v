Require Import Reals Lra Lia ZArith.ZArith Coq.Logic.FunctionalExtensionality List.
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

Lemma lemma_1_4_vi : forall x : R,
  x > (-1 + sqrt 5) / 2 \/ x < (-1 - sqrt 5) / 2 <-> x^2 + x + 1 > 2.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- 
Abort.

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
  (x - Rpower 2 (1/3)) * (x - Rpower 2 (1/2)) > 0.
Proof.
  intros x.  
Abort.

Lemma lemma_1_4_xi : forall x : R,
  Rpower 2 x < 8.
Proof.

Abort.

Lemma lemma_1_4_xii : forall x : R,
  x + Rpower 3 x < 4.
Proof.

Abort.

Lemma lemma_1_4_xiii : forall x : R,
  1 / x + 1 / (1 - x) > 0.
Proof.

Abort.

Lemma lemma_1_4_xiv : forall x : R,
  (x - 1) / (x + 1) > 0.
Proof.

Abort.

Definition XOR (P Q : Prop) : Prop :=
  (P \/ Q) /\ (~P \/ ~Q).

Definition P10' := forall r1 r2 : R, XOR (r1 = r2) (XOR (r1 < r2) (r2 < r1)).
Definition P11' := forall r1 r2 r3 : R, r1 < r2 /\ r2 < r3 -> r1 < r2.
Definition P12' := forall r1 r2 r3 : R, r1 < r2 -> r1 + r3 < r2 + r3.
Definition P13' := forall r1 r2 r3 : R, r1 < r2 /\ 0 < r3 -> r1 * r3 < r2 * r3.

Definition P10 := forall (P : R -> Prop) (r : R),
  (P r -> r > 0) -> XOR (r = 0) (XOR (P r) (P (-r))).

Definition P11 := forall (P : R -> Prop) (r1 r2 : R),
  (forall r : R, P r -> r > 0) -> (P r1 /\ P r2) -> P (r1 + r2).

Definition P12 := forall (P : R -> Prop) (r1 r2 : R),
  (forall r : R, P r -> r > 0) -> (P r1 /\ P r2) -> P (r1 * r2).

Lemma lemma_1_8_P10 : P10' -> P10.
Proof.
  intros H. unfold P10' in H. unfold P10. unfold XOR in *.
  intros P r H1. split.
  - Abort. 

Fixpoint fold_right' (l: list R) : R :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => x + fold_right' xs
  end.

Inductive expr : Type :=
| Num (n : R)
| Sum (e1 e2 : expr).

Fixpoint eval (e : expr) : R :=
  match e with
  | Num n => n
  | Sum e1 e2 => (eval e1) + (eval e2)
  end.

Fixpoint elements (e : expr) : list R :=
  match e with
  | Num n => [n]
  | Sum e1 e2 => elements e1 ++ elements e2
  end.

Lemma lemma_1_24_a : forall (l : list R) (a : R),
  fold_right' l + a  = fold_right' (l ++ [a]).
Proof.
  intros l a. induction l as [| a' l' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. destruct l' as [| a'' l''] eqn:El.
    -- simpl. lra.
    -- simpl. lra.
Qed.

Lemma lemma_1_24_b : forall l1 l2,
  fold_right' (l1 ++ l2) = fold_right' l1 + fold_right' l2.
Proof.
  intros l1 l2. generalize dependent l1.
  induction l2 as [| a l2' IH].
  - intros l1. rewrite app_nil_r. simpl. lra.
  - intros l1. replace (fold_right' (a :: l2')) with (a + fold_right' l2'). 
    2 : { simpl. destruct l2'. simpl. lra. simpl. reflexivity.  } 
    rewrite Rplus_comm. rewrite Rplus_assoc.
    replace (l1 ++ a :: l2') with ((l1 ++ [a]) ++ l2') by (rewrite <- app_assoc; reflexivity).
    rewrite IH. rewrite <- lemma_1_24_a. lra.
Qed.

Lemma lemma_1_24_c : forall (e : expr),
  eval e = fold_right' (elements e).
Proof.
  intros e. induction e as [n | e1 IH1 e2 IH2].
  - simpl. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. rewrite lemma_1_24_b. reflexivity.
Qed.

Lemma addition_assoc_nat : forall e1 e2 : expr,
  elements e1 = elements e2 -> eval e1 = eval e2.
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
           replace (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + choose k 0 * a ^ (k - 0 + 1) * b ^ 0 + (sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k))
           with (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) + choose k 0 * a ^ (k - 0 + 1) * b ^ 0 + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k) by lra.
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