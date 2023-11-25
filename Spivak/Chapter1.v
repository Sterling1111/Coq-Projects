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

Theorem pow_equ : forall (r: R) (a : nat),
  (a > 0)%nat -> r ^ a = r * r ^ (a - 1).
Proof.
  intros r a H1. destruct a.
  - lia.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
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

Lemma O_lt_7 : 0 <= 7. lra. Qed.

Lemma lemma_1_4_iii : forall x : R,
  x > Rsqrt (mknonnegreal 7 O_lt_7) \/ x < - Rsqrt (mknonnegreal 7 O_lt_7) <-> 5 - x^2 < - 2.
Proof.
  intros. split.
  - intros [H1 | H2].
    -- 
Admitted.
Proof.
  intro x. split.
  - intros [H1 | H2].
    -- apply Rplus_lt_reg_l with (r := 2).
  replace (2 + (5 - x ^ 2)) with (7 - x ^ 2) by lra. replace (2 + -2) with 0 by lra.
  apply Rplus_lt_reg_l with (r := -7). rewrite Rplus_0_r.
  replace (-7 + (7 - x ^ 2)) with (-x^2) by lra.
Abort.

Lemma lemma_1_4_iv : forall x : R,
  (x - 1) * (x - 3) > 0.
Proof.

Abort.

Lemma lemma_1_4_v : forall x : R,
  x^2 - 2 * x + 2 > 0.
Proof.

Abort.

Lemma lemma_1_4_vi : forall x : R,
  x^2 + x + 1 > 2.
Proof.

Abort.

Lemma lemma_1_4_vii : forall x : R,
  x^2 - x + 10 > 16.
Proof.

Abort.

Lemma lemma_1_4_viii : forall x : R,
  x^2 + x + 1 > 0.
Proof.

Abort.

Lemma lemma_1_4_ix : forall x : R,
  (x - PI) * (x + 5) * (x - 3) > 0.
Proof.

Abort.

Lemma lemma_1_4_x : forall x : R,
  (x - Rpower 2 (1/3)) * (x - Rpower 2 (1/2)) > 0.
Proof.

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


Open Scope nat_scope.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.


Definition choose (n k : nat) : nat :=
  (factorial n) / (factorial k * factorial (n - k)).

Lemma lemma_2_3 : forall n k : nat,
  (k >= 1)%nat -> (n >= k) ->
  choose (S n) k = choose n (k-1) + choose n k.
Proof.
  intros. unfold choose.
  simpl. destruct k.
  - lia.
  - destruct n.
    -- lia.
    -- simpl. destruct k.
      --- simpl. repeat rewrite Nat.add_0_r. rewrite Nat.sub_0_r.
