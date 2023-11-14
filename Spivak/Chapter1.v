Require Import Reals Lra Lia ZArith.ZArith Coq.Logic.FunctionalExtensionality.
From Fibonacci Require Import Strong_Induction.
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

Lemma sum_from_to_1' : forall f n,
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  destruct n; simpl; lra.
Qed.

Lemma sum_from_to_2' : forall n f,
  sum_f_R0 (fun x => f (S x)) n = sum_f_R0 f (S n) - f 0%nat.
Proof.
  intros. induction n.
  - simpl. lra.
  - simpl. rewrite IHn. rewrite sum_from_to_1'. lra.
Qed.

Lemma sum_from_to_2'' : forall n a f,
  sum_f_R0 (fun x => f (S (x + a))%nat) n = sum_f_R0 (fun x => f (x + a)%nat) (S n) - f a.
Proof.
  intros n a f.
  induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. rewrite sum_from_to_1'. simpl. lra.
Qed.

Lemma sum_from_to_equ_1': forall f i n,
  (i < n)%nat -> sum_f i n f = sum_f i (n-1) f + f n.
Proof.
  intros. induction n as [| k IH].
  - lia.
  - replace ((S k - 1)%nat) with (k%nat) by lia.
    assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite IH. 2 : { lia. }
       unfold sum_f. replace ((S k - i)%nat) with ((S (k - i))%nat) by lia.
       rewrite sum_from_to_1'. replace ((k - i)%nat) with (S (k - 1 - i)%nat) by lia.
       rewrite sum_from_to_1'. replace ((S (k - 1 - i) + i))%nat with (k%nat) by lia.
       replace ((S (S (k - 1 - i)) + i))%nat with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. unfold sum_f. replace ((S k - k)%nat) with 1%nat by lia.
       replace ((k - k)%nat) with 0%nat by lia. simpl. lra.
Qed.

Lemma sum_from_to_equ_2' : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f i n f = sum_f (i+1) n f + f i.
Proof.
  intros f i n H1.
  unfold sum_f. replace (n - i)%nat with (S (n - i - 1)) by lia.
  rewrite sum_from_to_1'. replace (S (n - i - 1) + i)%nat with n%nat by lia.
  replace ((fun x : nat => f (x + (i + 1))%nat)) with (fun x : nat => f (S x + i)%nat).
  rewrite sum_from_to_2'' with (a := i%nat). simpl. 
  replace (S (n - (i+1) + i)%nat) with n%nat by lia.
  replace (n - (i+1))%nat with (n - i - 1)%nat by lia. lra.
  apply functional_extensionality. intros x. replace (x + (i + 1))%nat with (S x + i)%nat by lia. lra.
Qed.

Lemma sum_from_to_equ_3' : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f (S i) n f = sum_f i n f - f i.
Proof.
  intros f i n H.
  unfold sum_f.
  induction n as [| k IH].
  - lia.
  - assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- replace ((S k - i)%nat) with (S(k - i)%nat) by lia.
       rewrite sum_from_to_1'. replace ((S (k - i) + i)%nat) with ((S k)%nat) by lia.
       replace (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) + f (S k) - f i)
       with (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) - f i + f (S k)) by lra. rewrite <- IH.
       2 : { lia. } replace ((S k - S i)%nat) with (S (k - S i)%nat) by lia. rewrite sum_from_to_1'.
       replace ((S (k - S i) + S i)%nat) with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. replace ((S k - k)%nat) with 1%nat by lia. replace ((S k - S k)%nat) with 0%nat by lia.
       simpl. lra.
Qed.

Lemma sum_from_to_equ_4 : forall f i n,
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
           rewrite sum_from_to_1'. replace (S k - i)%nat with (S (k - i))%nat by lia.
           rewrite sum_from_to_1'. replace ((S (k - i) + i)%nat) with (S k)%nat by lia.
           replace (S (S (k - i)) + i)%nat with (S (S k))%nat by lia. reflexivity.
       --- lia.
Qed.

Lemma sum_f_0_0 : forall f,
  sum_f 0 0 f = f 0%nat.
Proof.
  intros. unfold sum_f. simpl. lra.
Qed.

Lemma sum_f_a_a : forall f a,
  sum_f a a f = f a.
Proof.
  intros. unfold sum_f. rewrite Nat.sub_diag. simpl. lra.
Qed.

Lemma sum_f_mult_distributive :
  forall f l u x,
    x * (sum_f l u f) = sum_f l u (fun i => f i * x).
Proof.
  intros. unfold sum_f.
  set (k := (u - l)%nat).
  induction k as [| k' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. lra. 
Qed.

Lemma sum_from_to_congruence': forall (f g : nat -> R) (l u : nat),
(l <= u)%nat ->
(forall k, (l <= k <= u)%nat -> f k = g k) ->
sum_f l u f = sum_f l u g.
Proof.
  intros f g l u H1 H2.
  unfold sum_f. induction u as [| u' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (l = S u')%nat \/ (l < S u')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S u' - l)%nat with 0%nat by lia. simpl. rewrite H2.
       2 : { lia. } reflexivity.
    -- replace (S u' - l)%nat with (S (u' - l)%nat) by lia. repeat rewrite sum_from_to_1'.
       rewrite IH. 2 : { lia. } rewrite H2. 2 : { lia. } reflexivity. intros k H4. apply H2. lia.
Qed.

Theorem sums_equivalent' : forall (l u : nat) (x y : R) (f1 f2 : nat -> R),
  (l <= u)%nat ->
  (forall i : nat, (l <= i <= u )%nat -> f1 i = f2 i) ->
    sum_f l u f1 = sum_f l u f2.
Proof.
  intros l u x y f1 f2 H1 H2.
  apply sum_from_to_congruence'. apply H1. apply H2.
Qed.


Theorem sum_reindex' : forall (f : nat -> R) (l u s : nat),
  (s <= l <= u)%nat ->
  sum_f l u f = sum_f (l - s) (u - s) (fun i => f (i + s)%nat).
Proof.
  intros f l u s H.
  induction l as [| l' IH].
  - simpl. replace ((s)%nat) with (0%nat) by lia. rewrite Nat.sub_0_r.
    apply sum_from_to_congruence'. lia. intros k. replace ((k + 0)%nat) with (k%nat) by lia. reflexivity.
  - assert (H2 : (S l' = u)%nat \/ (S l' < u)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite H2. repeat rewrite sum_f_a_a. replace ((u - s + s)%nat) with ((u)%nat) by lia. reflexivity.
    -- rewrite sum_from_to_equ_3'. 2 : { lia. }
       assert (H3 : (s <= l')%nat \/ (s = S l')) by lia. destruct H3 as [H3 | H3].
       --- rewrite IH. 2 : { lia. }
            replace ((S l' - s)%nat) with (S (l' - s)%nat) by lia.
            rewrite sum_from_to_equ_3'. 2 : { lia. }
            replace ((l' - s + s)%nat) with ((l')%nat) by lia. lra.
       --- rewrite <- H3. replace ((S l' - S l')%nat) with (0%nat) by lia. simpl.
           unfold sum_f. replace ((u - s - (s - s))%nat) with ((u - s)%nat) by lia.
           replace ((u - l')%nat) with (S (u - s)%nat) by lia.
           rewrite sum_from_to_1'. simpl. replace ((S (u - s + l')%nat)) with u%nat by lia.
           set (f2 := fun x : nat => f (S (x + l'))%nat).
           replace (fun x : nat => f (x + (s - s) + s)%nat) with (fun x : nat => f (S x + l')%nat).
           2 : { apply functional_extensionality. intros x. replace (x + (s - s) + s)%nat with (x + S l')%nat by lia.
           replace (S x + l')%nat with (x + S l')%nat by lia. reflexivity. }
           replace (fun x : nat => f (S x + l')%nat) with f2. 2 : { apply functional_extensionality. unfold f2. simpl. reflexivity. }
           unfold f2. rewrite sum_from_to_2''. simpl. replace (S (u - s + l')%nat) with u%nat by lia. lra.
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
  - rewrite Rmult_minus_distr_r. rewrite sum_from_to_equ_1' at 1. 2: lia.
    replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
    replace ((n - (n - 1) - 1)%nat) with 0%nat by lia.
    replace (y ^ 0) with 1 by lra. rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_l. replace (x * x ^ (n - 1)) with (x ^ n). 
      2 : { destruct n. simpl. lia. simpl. rewrite Nat.sub_0_r. reflexivity. }
    assert (H3 : x * sum_f 0 (n - 2) (fun i : nat => x ^ i * y ^ (n - i - 1))
                = sum_f 0 (n - 2) (fun i : nat => x ^ (i + 1) * y ^ (n - 1 - i))).
      {
        rewrite sum_f_mult_distributive.
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
      rewrite H3. rewrite sum_from_to_equ_2' with (i := 0%nat) (n := (n-1)%nat). 2: lia.
      replace (x ^ 0) with 1 by lra. rewrite Rmult_1_l.
      replace ((n - 0 - 1)%nat) with (n - 1)%nat by lia.
      rewrite Nat.add_0_l.
      assert (H4 : y * (sum_f 1 (n - 1) (fun i : nat => x ^ i * y ^ (n - i - 1)) + y ^ (n - 1))
                = sum_f 1 (n - 1) (fun i : nat => x ^ i * y ^ (n - i)) + y ^ (n)).
        {
          rewrite Rmult_plus_distr_l. rewrite <- pow_equ. 2 : { lia. }
          rewrite sum_f_mult_distributive.
          set (f1 := fun i : nat => x ^ i * y ^ (n - i - 1) * y).
          set (f2 := fun i : nat => x ^ i * y ^ (n - i)).
          rewrite sums_equivalent' with (f1 := f1) (f2 := f2). reflexivity. auto. auto. lia.
          intros i. destruct i.
          - lia.
          - unfold f1. unfold f2. simpl. assert (H5 : (n - S i = 0)%nat \/ (n - S i > 0)%nat) by lia.
            destruct H5 as [H5 | H5].
            -- lia.
            -- rewrite pow_equ with (r := y) (a := (n - S i)%nat). 2 : { lia. } lra.
        }
      rewrite H4. rewrite sum_reindex' with (s := 1%nat) (l := 1%nat). 2 : { lia. }
      replace ((1 - 1)%nat) with 0%nat by lia. replace ((n - 1 - 1)%nat) with (n - 2)%nat by lia. 
      assert (H5 : sum_f 0 (n - 2) (fun i : nat => x ^ (i+1) * y ^ (n - 1 - i)) = 
                   sum_f 0 (n - 2) (fun i : nat => x ^ (i+1) * y ^ (n - (i+1)))).
        { apply sum_from_to_congruence'. lia. intros i H5. replace ((n - 1 - i)%nat) with (n - (i+1))%nat by lia. reflexivity. }
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


Theorem sum_n_nat : forall n : nat,
  sum_f 0 n (fun i => INR i) = (INR n * (INR n + 1)) / 2.
Proof.
  intros n. induction n as [| k IH].
  - rewrite sum_f_0_0. simpl. lra.
  - assert (H1 : (k = 0 \/ k > 0)%nat) by lia. destruct H1 as [H1 | H1].
    -- rewrite H1. unfold sum_f. simpl. lra.
    -- rewrite sum_from_to_equ_4. 2 : { lia. }
       rewrite IH. rewrite S_INR. lra.
Qed.

Example sheisa : sum_f 0 10 (fun i => INR i) = 55.
Proof. 
  rewrite sum_n_nat. simpl. lra.
Qed.