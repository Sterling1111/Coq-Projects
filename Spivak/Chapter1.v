Require Import Reals Lra Lia.
Require Import ZArith.ZArith.

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

Fixpoint sum_from_to' (f : nat -> nat -> R) (i n orig_n : nat) : R :=
  match n with
  | O => f i orig_n
  | S n' => f i orig_n + sum_from_to' f (S i) n' orig_n
  end.

Definition sum_from_to (f : nat -> nat -> R) (i n : nat) : R := 
  if (n <? i)%nat then 0 else sum_from_to' f i (n - i) n.

Lemma sum_from_to_ex : sum_from_to (fun i n => INR i) 0 3 = 6.
Proof. 
  unfold sum_from_to. simpl. lra.
Qed.

Lemma sum_from_to_equ : forall (f : nat -> nat -> R) (i n : nat),
  (i < n)%nat -> sum_from_to f i n = sum_from_to f i (n - 1) + f (n)% nat n.
Proof.
  intros f i n H. unfold sum_from_to. induction n as [| k IH].
  - inversion H.
  - assert (H1 : (S k <? i) = false). { apply Nat.ltb_ge. lia. }
    rewrite H1. destruct k.
    -- assert (i = 0)%nat by lia. rewrite H0. simpl. lra.

Lemma lemma_1_1_v : forall (x y : R) (n : nat),
  (n >= 1)%nat ->
  pow x n - pow y n = (x - y) * sum_from_to (fun i n => pow x i * pow y (n - i)) 0 (n-1).
Proof.
  intros. induction n as [| k IH].
  - lia.
  - destruct k.
    -- simpl. compute. lra.
    -- unfold sum_from_to.
      assert ( H1 : S (S k) - 1 <? 0 = false) by (compute; lia).
      rewrite H1. replace (x ^ (S (S k))) with (x * x ^ (S k)) by (simpl; lra).
      replace (y ^ (S (S k))) with (y * y ^ (S k)) by (simpl; lra). 
Qed.
