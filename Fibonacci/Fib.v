Require Import Peano ZArith Lia QArith Reals Nat.
Open Scope Z_scope.

Fixpoint fibonacci (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fibonacci(n') + fibonacci(n'')
            end
  end.

Global Notation F := fibonacci.

Lemma fib_suc_suc : forall n : nat, F (S (S n)) = F (S n) + F n.
Proof.
  intros n.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma fib_suc_suc' : forall n : nat, F(n+2) = F(n+1) + F(n).
Proof.
  intro n. 
  assert(H1: S n = (n+1)%nat).
    { lia. } rewrite <- H1.
  assert(H2: S (S n) = (n+2)%nat).
    { lia. } rewrite <- H2.
  apply fib_suc_suc.
Qed.

Lemma fib_suc_suc'' : forall n : nat, (n > 0)%nat -> F(n+1) = F(n) + F(n-1).
Proof.
  intros n H1. destruct n as [| n'] eqn:En.
  - simpl. exfalso. apply (Nat.lt_irrefl) in H1. apply H1.
  - assert (H2: S n' = (n' + 1)%nat).
    { lia. } rewrite -> H2. rewrite <- Nat.add_assoc. simpl.
    assert (H3: (n' + 1 - 1)%nat = n').
    { lia. } rewrite -> H3.
    apply fib_suc_suc'.
Qed.


Open Scope nat_scope.

Definition strong_induction_T (P : nat -> Prop) : Prop :=
  P 0 ->
  (forall n, (forall k, k <= n -> P k) -> P (S n)) ->
  forall n, P n.

Lemma strong_induction: forall P, strong_induction_T P.
Proof.
  unfold strong_induction_T.
  intros P Hbase Hstep.
  intros n.
  assert (forall k, k <= n -> P k).
  {
    induction n.
    - intros k Hkn. inversion Hkn. apply Hbase.
    - intros k Hkn. inversion Hkn.
      + apply Hstep. intros k0 Hk0n. apply IHn. lia.
      + apply IHn. lia.
  }
  apply H. lia.
Qed.

Close Scope nat_scope.

Open Scope Z_scope.

Lemma fibonacci_positive_strong : forall n, fibonacci n > 0.
Proof.
  apply strong_induction.
  - simpl. lia.
  - intros n IH. destruct n.
    + simpl. lia.
    + simpl. destruct n.
      ++ simpl. lia.
      ++ assert (H1: (S n <= S (S n))%nat). { lia. }
         assert (H2 : (n <= S (S n))%nat). { lia. }
         assert (H3 : F (S n) > 0). 
         { apply IH. apply H1. }
         assert (H4: F n > 0).
         { apply IH. apply H2. } lia.
Qed.

Lemma next_fib_greater : forall n : nat,
  fibonacci (S n) >= fibonacci n.
Proof.
  intro n. induction n as [| k IH].
  - simpl. lia.
  - rewrite -> fib_suc_suc. 
    assert (H1 : F (S k) > 0).
    { apply fibonacci_positive_strong. } 
    assert (H2 : F k > 0).
    { apply fibonacci_positive_strong. } lia.
Qed.

Check F.
About F.

Compute F(1) - F(5).
Compute F(3).
Compute F(5).

Lemma pow_2_z : forall (x : Z),
  x * x = Z.pow x 2.
Proof.
  intro z. unfold Z.pow. unfold Z.pow_pos. unfold Pos.iter.
  rewrite -> Z.mul_1_r. reflexivity.
Qed.

Lemma pow_add_one_nat : forall k : nat, (-1)^(Z.of_nat (k + 1)) = (-1)^(Z.of_nat k) * (-1)^1.
Proof.
  intros k.
  rewrite Nat2Z.inj_add. (* Converts (Z.of_nat (k + 1)) to (Z.of_nat k + 1) *)
  rewrite Z.pow_add_r.
  - reflexivity.
  - lia.
  - lia.
Qed.

Theorem fib_diff : forall (n : nat),
  F(n+2) * F(n) - (F(n+1) * F(n+1)) = (Z.pow (-1) (Z.of_nat n)).
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - replace (F (S k + 2)) with (F (k+2) + F(k + 1)).
    * rewrite -> Z.mul_add_distr_r. assert (H1: S k = (k+1)%nat).
      { rewrite -> Nat.add_comm. simpl. reflexivity. }
    rewrite -> H1.
    assert (H2: F ((k + 1 + 1)%nat) = F(k+2%nat)).
      { rewrite -> Nat.add_1_r. auto. }
    rewrite -> H2.
    assert (H3: F(k+1) * F(k+1) = F(k+2) * F(k) - (-1) ^ Z.of_nat k).
      { rewrite <- IH. lia.  }
    rewrite -> H3.
    assert (H4: F(k+2) * F(k+1) + (F(k+2) * F(k) - (-1) ^ Z.of_nat k) - F(k+2) * F(k+2) = 
                F(k+2) * (F(k) + F(k+1) - F(k+2)) - (-1) ^ Z.of_nat k).
  { lia. }
  rewrite H4.
  assert (H5: F(k) + F(k+1) = F(k+2)).
    { rewrite -> fib_suc_suc'. apply Z.add_comm. }
  rewrite -> H5. rewrite -> Z.sub_diag. rewrite -> Z.mul_0_r. 
  rewrite -> pow_add_one_nat. assert (H6: (-1)^1 = -1).
      { auto. } rewrite H6. lia.
    * assert(H1: (S k + 2)%nat = ((k+1) + 2)%nat).
      { lia. } rewrite H1.
      assert(H2 : F(k+1+2) = F(k+1+1) + F(k+1)).
        {rewrite <- fib_suc_suc'. reflexivity. } rewrite -> H2.
      assert(H3: (k+2)%nat = (k+1+1)%nat).
        { lia. } rewrite -> H3.
      reflexivity.
Qed.

Lemma lemma1 : forall n : nat,
  F(n+2) * F(n) - F(n+1) ^ 2 = (-1) ^ (Z.of_nat n).
Proof.
  intro n. rewrite <- pow_2_z. apply fib_diff.
Qed.

Example fib_test : F (3602) * F(3600) - F(3601)^2 = (-1)^(3600).
Proof. apply (lemma1 3600). Qed.

Compute F(15).
Compute F(20).
Compute F(25).

Compute ((inject_Z (F 10)) / (inject_Z (F 9)))%Q.

Definition a (n :nat) : Q :=
  match n with
  | O => 3
  | _ => (inject_Z (F(2 * n))) / (inject_Z (F(2 * n - 1)))
  end.

Compute a(0).
Compute a(1).
Compute a(2).
Compute a(3).
Compute a(4).

Definition b (n : nat) : Q := (inject_Z (F(2*n + 1))) / (inject_Z (F(2*n))).

Compute b(0).
Compute b(1).
Compute b(2).
Compute b(3).
Compute b(4).

Open Scope Z_scope.

Lemma lemmma : forall (n : nat), (n > 0)%nat -> (2 * n + 1)%nat = (2 * n - 1 + 2)%nat.
Proof.
  intros n H. induction n as [| k IH].
  - simpl. exfalso. apply (Nat.lt_irrefl) in H. apply H.
  - lia. 
Qed.

Search (_ - 0).

Check Z.pow_1_l.

Lemma odd_pow_neg : forall k, Nat.Odd k -> (-1) ^ Z.of_nat k = -1.
Proof.
  intros k Hodd.
  destruct Hodd as [m Heq]. 
  rewrite Heq.
  assert (Z.of_nat (2 * m + 1) = 2 * (Z.of_nat m) + 1).
  {
    rewrite Nat2Z.inj_add. 
    rewrite Nat2Z.inj_mul.
    reflexivity.
  }
  rewrite H. 
  rewrite Z.pow_add_r.
  - rewrite Z.pow_mul_r.
    -- rewrite Z.pow_1_r. rewrite Z.pow_2_r. simpl. rewrite Z.pow_1_l.
      --- reflexivity.
      --- lia.
    -- lia.
    -- lia.
  - lia.
  - lia.
Qed.

Lemma even_pow_pos : forall k, Nat.Even k -> (-1) ^ Z.of_nat k = 1.
Proof.
  intros k. unfold Nat.Even. intros [m Heq].
  assert (H2: (-1) ^ Z.of_nat (2 * m + 1) = -1).
  { apply odd_pow_neg. exists m. reflexivity. } 
  rewrite Heq. rewrite Nat2Z.inj_add in H2. rewrite Z.pow_add_r in H2.
  - assert (H3 : (-1) ^ Z.of_nat 1 = -1). { lia. } rewrite H3 in H2.
    lia.
  - lia.
  - lia.
Qed.

Lemma pow_n_squared_plus_1_unknown_sign : exists n m : nat,
  (-1) ^ Z.of_nat (n * n + 1) = -1 /\ (-1) ^ Z.of_nat (m * m + 1) = 1.
Proof.
  exists 2%nat. exists 1%nat. split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Lemma lemma2 : forall (n : nat), 
  (n > 0)%nat -> F(2*n+1)*F(2*n-1) - F(2*n)^2 < 0.
Proof.
  intros n H. rewrite -> lemmma. replace (F (2 * n)) with (F (2 * n - 1 + 1)).
  rewrite -> lemma1. induction n.
  - simpl. exfalso. apply (Nat.lt_irrefl) in H. apply H.
  - simpl. rewrite Nat.add_0_r. assert (H2: (n + S n - 0)%nat = (2 * n + 1)%nat).
    { lia. } rewrite -> H2.
    assert (H3: (-1) ^ Z.of_nat (2 * n + 1) = -1).
    { apply odd_pow_neg. exists n. reflexivity. } rewrite H3. lia.
  - assert (H2 : (2 * n - 1 + 1 = 2 * n)%nat). { lia. } rewrite -> H2. reflexivity.
  - apply H.
Qed.

Lemma lemma3 : forall (n : nat),
  (n > 0)%nat -> F(2*n+1)*F(2*n-1) < F(2*n)^2.
Proof.
  intros n H. apply lemma2 in H. lia.
Qed.

Lemma lemma4 : forall (n : nat),
  (n > 0)%nat -> F (2*n) * F(2*n-1) + F(2*n+1)*F(2*n-1) < F(2*n)^2 + F(2*n) * F(2*n-1).
Proof.
  intros n H. apply lemma3 in H. lia.
Qed.

Lemma lemma5 : forall (n : nat),
  (n > 0)%nat -> F(2*n-1) * (F (2*n+1) + F(2*n)) < F (2*n) * (F (2*n) + F (2*n-1)).
Proof.
  intros n H. apply lemma4 in H. lia.
Qed.

Lemma lemma6 : forall (n : nat),
  (n > 0)%nat -> (F(2*n-1) * F(2*n+2)) < (F(2*n) * F(2*n+1)).
Proof.
  intros n H. 
  replace (F (2 * n + 2)) with (F (2 * n + 1) + F (2 * n)).
  replace (F (2 * n + 1)) with (F (2 * n) + F (2 * n - 1)) at 2.
  - apply lemma5 in H. lia.
  - apply symmetry. apply fib_suc_suc'' with (n := (2 * n)%nat). lia.
  - apply symmetry. apply fib_suc_suc' with (n := (2 * n)%nat).
Qed.

Open Scope Q_scope.

Lemma inject_Z_mul : forall a b : Z, inject_Z (a * b) == inject_Z a * inject_Z b.
Proof.
  intros.
  unfold Qmult, inject_Z. simpl.
  reflexivity.
Qed.

Lemma inject_Z_lt : forall a b : Z,
  (a < b)%Z -> inject_Z a < inject_Z b.
Proof.
  intros a b. unfold inject_Z. unfold Qlt. simpl. 
  repeat rewrite Z.mul_1_r. auto.
Qed.

Lemma div_Q : forall (a b c d : Q),
  (a > 0) /\ (c > 0) /\ (a * b < c * d) -> b / c < d / a.
Proof.
  intros a b c d [H1 [H2 H3]].
  assert (H4 : b < (c * d) / a).
  { apply Qlt_shift_div_l. apply H1. rewrite Qmult_comm. apply H3. }
  apply Qlt_shift_div_r.
  - apply H2.
  - rewrite Qmult_comm. unfold Qdiv in H4. unfold Qdiv. rewrite <- Qmult_assoc in H4.
    apply H4.
Qed.

Lemma inject_Z_gt_0 : forall a : Z,
  (a > 0)%Z -> inject_Z a > 0.
Proof.
  intros a. unfold inject_Z. unfold Qlt. simpl.
  rewrite Z.mul_1_r. intro H. apply Z.gt_lt in H. apply H.
Qed.

Lemma lemma7 : forall (n : nat),
  (n > 0)%nat -> 
  inject_Z (F ((2 * n + 2))) / inject_Z (F (2 * n + 1)) < 
  inject_Z (F (2 * n)) / inject_Z (F (2 * n - 1)).
Proof.
  intros n H1. apply lemma6 in H1. 
  assert (H2 : inject_Z (F (2 * n - 1)) * inject_Z (F (2 * n + 2)) <
             inject_Z (F (2 * n)) * inject_Z (F (2 * n + 1))).
         { repeat rewrite <- inject_Z_mul. apply inject_Z_lt. apply H1. }
  assert (H3 : (F (2 * n - 1) > 0)%Z).
         { apply fibonacci_positive_strong with (n := (2 * n - 1)%nat). }
  assert (H4 : (F (2 * n + 1) > 0)%Z).
         { apply fibonacci_positive_strong with (n := (2 * n + 1)%nat). }
  assert (H5 : inject_Z (F (2 * n - 1)) > 0).
         { apply inject_Z_gt_0. apply H3. }
  assert (H6 : inject_Z (F (2 * n + 1)) > 0).
         { apply inject_Z_gt_0. apply H4. }
  apply div_Q. split.
  - apply H5.
  - split.
    + apply H6.
    + rewrite Qmult_comm with (x := inject_Z (F (2 * n + 1))) (y := inject_Z (F (2 * n))). apply H2.
Qed.

Lemma a_decreasing : forall (n : nat),
  (n > 0)%nat -> a (S n) < a n.
Proof.
  intros n H1.
  unfold a. destruct n.
  - simpl. lia.
  - assert (H2 : (2 * S (S n) = (2 * S n + 2))%nat).
    { lia. } rewrite -> H2 at 1. 
    assert (H3 : (2 * S (S n) - 1 = (2 * (S n) + 1))%nat).
    { lia. } rewrite -> H3.
    apply lemma7. apply H1.
Qed.

Example a_test: a (10) < a (9).
Proof.
  simpl. unfold Qlt. simpl. reflexivity. Qed.


Example a_test2: a (100) < a (99).
Proof.
  apply a_decreasing. lia. Qed.

Lemma a_bounded_below : forall (n : nat),
  (n > 0)%nat -> a n > 0.
Proof.
  intros n H1. unfold a. destruct n.
  - lia.
  - assert (H2 : (2 * S n - 1 = (2 * n + 1))%nat).
    { lia. } rewrite -> H2.
    assert (H3 : (F (2 * n + 1) > 0)%Z).
    { apply fibonacci_positive_strong with (n := (2 * n + 1)%nat). }
    assert (H4 : (F (2 * S n) > 0)%Z).
    { apply fibonacci_positive_strong with (n := (2 * S n)%nat). }
    apply inject_Z_gt_0 in H3. apply inject_Z_gt_0 in H4.
    unfold Qdiv. apply Qmult_lt_0_compat. apply H4.
    apply Qinv_lt_0_compat. apply H3.
Qed.


Example a_test3: a (10) > 0.
Proof.
  simpl. unfold Qlt. simpl. reflexivity. Qed.

Example a_test4: a (100) > 0.
Proof.
  apply a_bounded_below. lia. Qed.

Close Scope Q_scope.

Lemma lemma8 : forall (n : nat),
  F (2*n+2) * F(2*n) - F(2*n + 1)^2 = 1.
Proof.
  intro n. rewrite lemma1 with (n := (2 * n)%nat).
  apply even_pow_pos. exists n. lia.
Qed.

Open Scope R_scope.

(* Define a sequence as a function from natural numbers to reals *)
Definition sequence := nat -> R.

(* Stating that a sequence is strictly decreasing *)
Definition strictly_decreasing (a : sequence) : Prop :=
  forall n : nat, a n > a (S n).

Definition strictly_increasing (a : sequence) : Prop :=
  forall n : nat, a n < a (S n).

(* Stating that a sequence is bounded below *)
Definition bounded_below (a : sequence) (LB : R) : Prop :=
  forall n : nat, LB < a n.

Definition bounded_above (a : sequence) (UB : R) : Prop := 
  forall n : nat, UB > a n.

(* Monotonic Sequence Theorem for strictly decreasing sequences *)
Axiom Monotonic_Sequence_Theorem :
  forall (a : sequence) (LB UB : R),
  ((strictly_decreasing a /\ bounded_below a LB) \/
  (strictly_increasing a /\ bounded_above a UB)) ->
  exists L : R,
    (forall e : R, e > 0 ->
     exists N : nat, forall n : nat, (n > N)%nat -> Rabs (a n - L) < e).

Close Scope R_scope.

Example poop : (2 + 2 = 4)%nat.
Proof. lia. Qed. 