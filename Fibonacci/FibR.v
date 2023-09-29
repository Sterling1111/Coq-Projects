Require Import Peano ZArith Lia QArith Reals Nat Lra Classical.

Open Scope R_scope.

Fixpoint fibonacci (n : nat) : R :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fibonacci(n') + fibonacci(n'')
            end
  end.

Global Notation F := fibonacci.

Lemma fib_S_S_n : forall n : nat, F (S (S n)) = F (S n) + F n.
Proof.
  intros n.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma fib_n_plus_2 : forall n : nat, F(n+2) = F(n+1) + F(n).
Proof.
  intro n. 
  replace ( (n + 1)%nat ) with ( S n )%nat by lia.
  replace ( (n + 2)%nat ) with ( S (S n) )%nat by lia.
  apply fib_S_S_n.
Qed.

Lemma fib_n_plus_1 : forall n : nat, (n > 0)%nat -> F(n+1) = F(n) + F(n-1).
Proof.
  intros n H1. destruct n as [| n'] eqn:En.
  - simpl. exfalso. apply (Nat.lt_irrefl) in H1. apply H1.
  - replace ( (S n') ) with ( (n' + 1)%nat ) by lia. 
    rewrite <- Nat.add_assoc. simpl.
    replace ( (n' + 1 - 1)%nat ) with ( n' ) by lia.
    apply fib_n_plus_2.
Qed.

Lemma fib_n_plus_3 : forall n : nat, F(n+3) = F(n+2) + F(n+1).
Proof.
  intro n. 
  replace ( (n + 2)%nat ) with ( (n + 1 + 1)%nat ) by lia.
  replace ( (n + 3)%nat ) with ( (n + 1 + 2)%nat ) by lia.
  apply fib_n_plus_2.
Qed.

Open Scope nat_scope.

Lemma strong_induction (P : nat -> Prop) :
  P 0 ->
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros H1 H2 n. enough (H0: forall k, k <= n -> P k).
  - apply H0. lia.
  - induction n.
    -- intros k Hk. inversion Hk. apply H1.
    -- intros k Hk. apply H2. intros k' Hk'. apply IHn. lia.
Qed.

Open Scope R_scope.

Lemma fib_n_ge_1 : forall n, F n >= 1.
Proof.
  apply strong_induction.
  - simpl. lra.
  - intros n IH. destruct n.
    + simpl. lra.
    + simpl. destruct n.
      ++ simpl. lra.
      ++ assert (H1: (S n <= S (S n))%nat) by lia.
         assert (H2 : (n <= S (S n))%nat) by lia.
         assert (H3 : F (S n) >= 1) by (apply IH; lia).
         assert (H4: F n >= 1) by (apply IH; lia).
         lra.
Qed.

Lemma fib_n_gt_0 : forall n, F n > 0.
Proof.
  intros n. assert (H1 : F n >= 1) by apply fib_n_ge_1. lra.
Qed.

Lemma fib_Sn_ge_fib_n : forall n : nat,
  F (S n) >= F n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - rewrite -> fib_S_S_n.  
    assert (H1 : F (S k) > 0) by apply fib_n_gt_0.
    assert (H2 : F k > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n_ge_1_imp_fib_Sn_gt_fib_n : forall n : nat,
  (n >= 1)%nat -> F (S n) > F n.
Proof.
  intros n H. destruct n as [| n'] eqn:En.
  - lia.
  - rewrite -> fib_S_S_n. 
    assert (H1 : F (S n') > 0) by apply fib_n_gt_0.
    assert (H2 : F n' > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n1_ge_n2_imp_fib_n1_ge_fib_n2 : forall (n1 n2 : nat),
  (n1 >= n2)%nat -> F n1 >= F n2.
Proof.
  intros n1 n2 H.
  induction H.
  - lra.
  - assert (H2 : F (S m) >= F m)  by apply fib_Sn_ge_fib_n.
    lra.
Qed.

Lemma fib_n_ge_n : forall n : nat,
  F n >= INR n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ( (S k) ) with ( (k + 1)%nat ) by lia.
    destruct k as [| k'] eqn:Ek.
    -- simpl. lra.
    -- rewrite fib_n_plus_1.
       --- rewrite plus_INR. 
           assert (H1 : F (S k' - 1) >= 1) by apply fib_n_ge_1.
           replace ( (INR 1) ) with ( (1) ) by (simpl; lra). lra.
       --- lia.
Qed.
    
Lemma fib_2n_ge_fib_n : forall n : nat,
  F (2 * n) >= F n.
Proof.
  intros n. assert (H : (2 * n >= n)%nat) by lia.
  apply n1_ge_n2_imp_fib_n1_ge_fib_n2. apply H.
Qed.

Lemma fib_2n_times_fib_n_ge_n : forall n : nat,
  F (2 * n) * F (2 * n - 1) >= F n.
Proof.
  intro n. assert (H1 : F ((2 * n)%nat) > 0) by apply fib_n_gt_0.
  assert (H2 : F ((2 * n - 1)%nat) >= 1) by apply fib_n_ge_1.
  assert (H3 : F ((2 * n)%nat) >= F n) by apply fib_2n_ge_fib_n.
  apply Rmult_ge_compat_l with (r := F (2 * n)%nat) in H2.
  - rewrite Rmult_1_r in H2. lra.
  - apply Rgt_ge. apply H1. 
Qed.

Lemma fib_prod_ge_n : forall (n : nat),
  F (2 * n) * F (2 * n - 1) >= INR n.
Proof.
  intros n. 
  assert (H1 : F (2 * n) * F (2 * n - 1) >= F n) by apply fib_2n_times_fib_n_ge_n.
  assert (H2 : F n >= INR n) by apply fib_n_ge_n.
  apply Rge_trans with (r3 := INR n) in H1.
  - apply H1.
  - apply H2.
Qed.

Lemma Rpow_neg1_n_plus_1 : forall (n : nat),
  (-1) ^ (n + 1) = (-1) ^ n * (-1) ^ 1.
Proof.
  intros n.
  induction n.
  - simpl. lra.
  - simpl. rewrite IHn. lra.
Qed.

Lemma lemma1 : forall (n : nat),
  F(n+2) * F n - (F(n+1))^2 = (-1)^n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ( ((S k + 2)%nat) ) with ( (k+3)%nat ) by lia.
    replace ( (S k) ) with ( (k+1)%nat ) by lia.
    replace ( (k + 1 + 1)%nat ) with ( (k + 2)%nat ) by lia.
    replace ( (F(k+3)) ) with ( (F(k+2) + F(k+1)) ) by (rewrite fib_n_plus_3; reflexivity).
    rewrite Rmult_plus_distr_r.
    assert (Hnew: F (k + 1) ^ 2 = F (k + 2) * F k - (-1) ^ k) by (rewrite <- IH; lra).
    clear IH. rename Hnew into IH.
    replace ( F(k+1) * F(k+1) ) with ( F(k+1)^2 ) by lra.
    rewrite IH.
    replace ( F(k+2) * F(k+1) + (F(k+2) * F k - (-1)^k) - F(k+2)^2 ) with 
            ( F(k+2) * (F k + F(k+1) - F(k+2)) - (-1)^k) by lra.
    rewrite Rplus_comm.
    replace ( F(k+1) + F k ) with ( F(k+2) ) by (rewrite <- fib_n_plus_2; reflexivity).
    rewrite Rpow_neg1_n_plus_1. lra.
Qed.

Definition a (n : nat) : R :=
  match n with
  | 0 => 2
  | _ => F(2*n) / F(2*n-1)
  end.

Lemma a_decreasing : .
Proof.
  
Qed.
  