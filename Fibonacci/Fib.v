Require Import Peano ZArith Lia QArith Reals Nat Reals.

Open Scope Z_scope.

Check Rinv_0.

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

Lemma fib_suc_suc''' : forall n : nat, F(n+3) = F(n + 2) + F(n+1).
Proof.
  intro n. destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - assert (H1: (S n' + 3 = (S n' + 1) + 2)%nat).
    { lia. } rewrite H1.
    assert (H2: (S n' + 2 = (S n' + 1) + 1)%nat).
    { lia. } rewrite H2.
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

Lemma next_fib_greater' : forall n : nat,
  (n >= 1)%nat -> fibonacci (S n) > fibonacci n.
Proof.
  intros n H. destruct n as [| n'] eqn:En.
  - lia.
  - rewrite -> fib_suc_suc. 
    assert (H1 : F (S n') > 0).
    { apply fibonacci_positive_strong. } 
    assert (H2 : F n' > 0).
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

Definition unject_Z (q : Q) : Z :=
  Qnum q.

Lemma unject_inject_Z : forall (z : Z),
  unject_Z (inject_Z z) = z.
Proof.
  intro z. unfold unject_Z. unfold inject_Z. simpl. reflexivity.
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

Definition Q_seq := nat -> Q.
Definition seq := nat -> R.

Definition a (n :nat) : Q :=
  match n with
  | O => 2
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

Lemma inject_Z_plus : forall a b : Z, inject_Z (a + b) == inject_Z a + inject_Z b.
Proof.
  intros.
  unfold Qplus, inject_Z. simpl. repeat rewrite Z.mul_1_r. reflexivity.
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

Lemma div_Q' : forall (a b c d : Q),
  (a > 0) /\ (c > 0) /\ (a * b > c * d) -> b / c > d / a.
Proof.
  intros a b c d [H1 [H2 H3]].
  assert (H4 : b > (c * d) / a).
  { apply Qlt_shift_div_r. apply H1. rewrite (Qmult_comm b a). apply H3. }
  apply Qlt_shift_div_l.
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

Lemma a_decreasing_strict : forall (n : nat),
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

Definition Q_seq_decreasing (a : Q_seq) : Prop :=
  forall (n : nat), a (S n) <= a n.

Definition Q_seq_increasing (a : Q_seq) : Prop := 
  forall (n : nat), a (S n) >= b n.

Definition Q_seq_bounded_below (a : Q_seq) : Prop :=
  exists (LB : Q), forall (n : nat), a n >= LB.

Definition Q_seq_bounded_above (a : Q_seq) : Prop :=
  exists (UB : Q), forall (n : nat), a n <= UB.

Lemma a_Q_decreasing : Q_seq_decreasing a.
Proof.
  intros n. destruct n.
  - simpl. unfold Qle. simpl. reflexivity.
  - apply Qlt_le_weak. apply a_decreasing_strict. lia.
Qed.

Example a_test: a (10) < a (9).
Proof.
  simpl. unfold Qlt. simpl. reflexivity. Qed.


Example a_test2: a (100) < a (99).
Proof.
  apply a_decreasing_strict. lia. Qed.

Lemma a_bounded_below : Q_seq_bounded_below a.
Proof.
  unfold a. unfold Q_seq_bounded_below. exists 0. intro n. destruct n.
  - unfold Qle. simpl. lia.
  - assert (H2 : (2 * S n - 1 = (2 * n + 1))%nat).
    { lia. } rewrite -> H2.
    assert (H3 : (F (2 * n + 1) > 0)%Z).
    { apply fibonacci_positive_strong with (n := (2 * n + 1)%nat). }
    assert (H4 : (F (2 * S n) > 0)%Z).
    { apply fibonacci_positive_strong with (n := (2 * S n)%nat). }
    apply inject_Z_gt_0 in H3. apply inject_Z_gt_0 in H4.
    unfold Qdiv. apply Qmult_le_0_compat.
    -- apply Qlt_le_weak. apply H4.
    -- apply Qinv_le_0_compat. apply Qlt_le_weak. apply H3.
Qed.

Example a_test3: a (0) >= 0.
Proof.
  simpl. unfold Qlt. simpl. apply Qlt_le_weak. reflexivity. Qed.

Close Scope Q_scope.

Lemma lemma8 : forall (n : nat), (n >= 0)%nat ->
  F (2*n+2) * F(2*n) - F(2*n + 1)^2 = 1.
Proof.
  intros n H1. rewrite lemma1 with (n := (2 * n)%nat).
  apply even_pow_pos. exists n. lia.
Qed.

Lemma lemma9 : forall (n : nat), (n >= 0)%nat ->
  F (2*n+2) * F(2*n) - F(2*n + 1)^2 > 0.
Proof.
  intros n H1. rewrite lemma8. lia. lia.
Qed.

Lemma lemma10 : forall (n : nat), (n >= 0)%nat ->
  F (2*n+2) * F(2*n) > F(2*n + 1)^2.
Proof.
  intros n H. apply lemma9 in H. lia.
Qed.

Lemma lemma11 : forall (n : nat), (n >= 0)%nat ->
  F (2*n) * F(2*n+1) + F(2*n + 2) * F (2 * n) > F(2*n + 1)^2 + F(2*n) * F(2*n+1).
Proof.
  intros n H. apply lemma10 in H. lia.
Qed.

(*create lemma12 which is the same as lemma11 but factor out F(2n) on the left and
  factor out F(2n+1) on the right*)

Lemma lemma12 : forall (n : nat), (n >= 0)%nat ->
  F (2*n) * (F(2*n+1) + F(2*n+2)) > F(2*n + 1) * (F(2*n+1) + F(2*n)).
Proof.
  intros n H. apply lemma11 in H. lia.
Qed.

(*create lemma13 which converts the part of both products which is a sum to the next larger fib nubmer*)

Lemma lemma13: forall (n : nat), (n >= 0)%nat ->
  F(2*n) * F (2*n + 3) > F(2*n + 1) * F(2*n + 2).
Proof.
  intros n H. apply lemma12 in H. rewrite <- fib_suc_suc' in H. rewrite fib_suc_suc'''.
  lia.
Qed.

Open Scope Q_scope.

Lemma lemma14 : forall (n : nat),
  (n >= 0)%nat ->
  inject_Z (F ((2 * n + 3))) / inject_Z (F (2 * n + 2)) > 
  inject_Z (F (2 * n + 1)) / inject_Z (F (2 * n)).
Proof.
  intros n H1. apply lemma13 in H1.
  assert (H2 : inject_Z (F (2 * n)) * inject_Z (F (2 * n + 3)) >
               inject_Z (F (2 * n + 1)) * inject_Z (F (2 * n + 2))).
         { repeat rewrite <- inject_Z_mul. apply inject_Z_lt. lia. }
  assert (H3 : (F (2 * n) > 0)%Z).
         { apply fibonacci_positive_strong with (n := (2 * n)%nat). }
  assert (H4 : (F (2 * n + 2) > 0)%Z).
         { apply fibonacci_positive_strong with (n := (2 * n + 2)%nat). }
  assert (H5 : inject_Z (F (2 * n)) > 0).
         { apply inject_Z_gt_0. apply H3. }
  assert (H6 : inject_Z (F (2 * n + 2)) > 0).
         { apply inject_Z_gt_0. apply H4. }
  apply div_Q'. split.
  - apply H5.
  - split.
    + apply H6.
    + rewrite Qmult_comm with (x := inject_Z (F (2 * n + 2))) (y := inject_Z (F (2 * n + 1))). apply H2.
Qed.

Lemma b_Q_increasing : Q_seq_increasing b.
Proof.
  intros n. apply Qlt_le_weak. unfold b. destruct n.
  - simpl. apply Qlt_shift_div_l.
    -- reflexivity.
    -- reflexivity.
  - assert (H2 : (2 * S (S n) + 1 = 2 * S n + 3)%nat).
    { lia. } rewrite H2.
    assert (H3 : (2 * S (S n) = 2 * (S n) + 2)%nat).
    { lia. } rewrite H3.
    apply lemma14. lia.
Qed.

Lemma lemma15 : forall (n : nat), 
  (n >= 1)%nat -> (inject_Z (F n)) / (inject_Z (F (S n))) < 1.
Proof.
  intros n H1. destruct n.
  - lia.
  - apply Qlt_shift_div_r.
    + assert (H2 : (F (S (S n)) > 0)%Z).
      { apply fibonacci_positive_strong with (n := (S (S n))%nat). }
      apply inject_Z_gt_0 in H2. apply H2.
    + rewrite Qmult_1_l. assert (H3 : (F (S n) < F (S (S n)))%Z).
      { apply next_fib_greater' in H1. lia. } 
      apply inject_Z_lt in H3. apply H3.
Qed.

Lemma lemma16 : forall (n : nat),
  (n >= 2)%nat -> (inject_Z (F (n-1))) / (inject_Z (F (n))) < 1.
Proof.
  intros n H1. destruct n.
  - lia.
  - assert (H2: (S (S n - 1) = S n)%nat).
    { lia. } rewrite <- H2 at 2. apply lemma15. lia.
Qed.

Lemma lemma17 : b 0 < 2.
Proof.
  unfold b. simpl. unfold Qlt. simpl. reflexivity.
Qed.

Lemma lemma18 : b 1 < 2.
Proof.
  unfold b. simpl. unfold Qlt. simpl. reflexivity.
Qed.

Lemma lemma19: forall (n : nat),
  (n >= 2)%nat -> b n < 2.
Proof.
  intros n H1. unfold b. rewrite fib_suc_suc''. 
  - unfold Qdiv. rewrite Qmult_comm. rewrite inject_Z_plus.
    rewrite Qmult_plus_distr_r. rewrite Qmult_comm. rewrite Qmult_inv_r.
    -- assert (H3 : / inject_Z (F (2 * n)) * inject_Z (F (2 * n - 1)) < 1).
      { rewrite Qmult_comm. apply lemma16. lia. }
      replace (2) with (1 + 1). rewrite Qplus_comm.
      apply Qplus_lt_le_compat.
      --- apply H3.
      --- apply Qle_refl.
      --- auto.
    -- assert (H2 : (F (2 * n) > 0)%Z).
      { apply fibonacci_positive_strong with (n := (2 * n)%nat). }
      apply inject_Z_gt_0 in H2. unfold not. intro H3. rewrite H3 in H2. inversion H2.
- lia. 
Qed.

Lemma b_bounded_above : forall (n : nat),
  b n < 2.
Proof.
  intro n. destruct n.
  - apply lemma17.
  - destruct n.
    -- apply lemma18.
    -- apply lemma19. lia.
Qed.

Lemma b_Q_bounded_above : Q_seq_bounded_above b.
Proof.
  unfold Q_seq_bounded_above. exists 2. intro n. apply Qlt_le_weak. apply b_bounded_above.
Qed. 

Definition c (n : nat) : Q := inject_Z (F (2 * n + 1)) / inject_Z (F (2 * n)).

Compute c (0).
Compute c (1).
Compute c (2).
Compute c (3).
Compute c (4).
Compute c (5).
Compute c (6).

Lemma Qmult_minus_distr_l : forall a b c : Q,
  a * (b - c) == a * b - a * c.
Proof.
  intros a b c.
  
  unfold Qminus, Qmult.
  unfold Qeq.
  simpl.
  lia.
Qed.

Lemma lemma21 : forall a b c d : Q,
  (b > 0) /\ (d > 0) -> d * / d * (a * / b) == (/b * /d) * (a * d).
Proof.
  intros a b c d H.
  destruct H as [H1 H2].
  rewrite Qmult_inv_r. 
      - rewrite Qmult_1_l. 
        rewrite Qmult_comm with (x := a) (y := d).
        rewrite Qmult_assoc.
        rewrite <- Qmult_assoc with (n := /b) (m := /d) (p := d).
        rewrite Qmult_comm with (x := /d) (y := d).
        rewrite Qmult_inv_r.
          -- rewrite Qmult_1_r. apply Qmult_comm.
          -- unfold not. intro H5. rewrite H5 in H2. inversion H2.
      - unfold not. intro H5. rewrite H5 in H2. inversion H2.
Qed.


Lemma lemma20 : forall (a b c d : Q),
  (b > 0) /\ (d > 0) -> a / b - c / d == (a * d - b * c) / (b * d).
Proof.
  intros a b c d [H1 H2]. unfold Qdiv.
  assert (H3 : ((d * / d) * (a * / b) == a * / b)).
    { 
      rewrite Qmult_inv_r.
      - rewrite Qmult_1_l. reflexivity.
      - unfold not. intro H3. rewrite H3 in H2. inversion H2.
    }
  assert (H4 : ((b * / b) * (c * / d) == c * / d)).
    {
      rewrite Qmult_inv_r.
      - rewrite Qmult_1_l. reflexivity.
      - unfold not. intro H4. rewrite H4 in H1. inversion H1.
    }
  rewrite <- H3. rewrite <- H4.
  rewrite lemma21.
  - rewrite lemma21.
    -- rewrite Qmult_comm with (x := /b) (y := /d). 
       rewrite <- Qmult_minus_distr_l. rewrite Qinv_mult_distr.
       rewrite Qmult_comm. rewrite Qmult_comm with (x := c) (y := b) at 1.
       rewrite Qmult_comm with (x := /b) (y := /d). reflexivity.
    -- auto.
    -- auto.
  - auto.
  - auto.
Qed.

Lemma inject_Z_minus : forall a b : Z,
  inject_Z (a - b) == inject_Z a - inject_Z b.
Proof.
  intros a b. unfold Qminus, inject_Z. simpl. unfold Qeq. simpl. lia.
Qed.

Lemma lemma1_Q : forall n : nat,
  inject_Z (F(n+2)) * inject_Z (F(n)) - inject_Z (F(n+1) ^ 2) == inject_Z ((-1) ^ (Z.of_nat n)).
Proof.
  intros n.
  rewrite <- inject_Z_mult. rewrite <- inject_Z_minus. rewrite lemma1. reflexivity.
Qed.

Lemma bn_minus_an : forall (n : nat), 
  b n - a n == -1 / (inject_Z (F (2*n)) * inject_Z (F(2*n - 1))).
Proof.
  intros n. unfold b. unfold a. destruct n.
  - simpl. reflexivity.
  - rewrite lemma20.
    -- assert (H2 : (2 * S n + 1 = 2 * S n - 1 + 2)%nat).
      { lia. } rewrite H2.
    assert (H3 : (2 * S n = 2 * S n - 1 + 1)%nat).
      { lia. } rewrite H3 at 3. rewrite H3 at 4.
    repeat rewrite <- inject_Z_mult. rewrite <- inject_Z_minus. rewrite <- Z.pow_2_r.
    rewrite -> lemma1.
    assert (H4 : (Nat.Odd (2 * S n - 1)%nat)).
      { exists n. lia. } rewrite -> odd_pow_neg.
      --- reflexivity.
      --- apply H4.
    -- split.
      --- assert (H2 : (F (2 * S n - 1) > 0)%Z).
          { apply fibonacci_positive_strong with (n := (2 * S n - 1)%nat). }
          assert (H3 : (F (2 * S n) > 0)%Z).
          { apply fibonacci_positive_strong with (n := (2 * S n)%nat). }
          apply inject_Z_gt_0 in H2. apply inject_Z_gt_0 in H3. apply H3.
      --- assert (H2 : (F (2 * S n - 1) > 0)%Z).
          { apply fibonacci_positive_strong with (n := (2 * S n - 1)%nat). }
          assert (H3 : (F (2 * S n) > 0)%Z).
          { apply fibonacci_positive_strong with (n := (2 * S n)%nat). }
          apply inject_Z_gt_0 in H2. apply inject_Z_gt_0 in H3. apply H2.
Qed.

Compute b 0 - a 0.
Compute b 1 - a 1.
Compute b 2 - a 2.
Compute b 3 - a 3.
Compute b 4 - a 4.

Compute b 4.
Compute (F 9).
Compute (F 8).

Compute a 4.

Compute 55 / 34.
Compute (b 4).

Open Scope R_scope.

Definition arbitrarily_small (a : nat -> R) :=
  forall eps : R, eps > 0 -> exists N : nat, forall (n : nat), (n >= N)%nat -> Rabs (a n) < eps.

(* Define a sequence as a function from natural numbers to reals *)
Definition sequence := nat -> R.

(* Stating that a sequence is strictly decreasing *)
Definition decreasing (a : sequence) : Prop :=
  forall n : nat, a n >= a (S n).

Definition increasing (a : sequence) : Prop :=
  forall n : nat, a n <= a (S n).

(* Stating that a sequence is bounded below *)
Definition bounded_below (a : sequence) (LB : R) : Prop :=
  forall n : nat, LB <= a n.

Definition bounded_above (a : sequence) (UB : R) : Prop := 
  forall n : nat, UB >= a n.

Definition limit_seq (a : nat -> R) (l : R) :=
  forall eps : R, eps > 0 ->
                  exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (a n - l) < eps.

(* Monotonic Sequence Theorem for strictly decreasing sequences *)
Axiom Monotonic_Sequence_Theorem :
  forall (a : sequence) (LB UB : R),
  ((decreasing a /\ bounded_below a LB) \/
  (increasing a /\ bounded_above a UB)) ->
  exists l : R, limit_seq a l.

Definition one_over_n (n : nat) : R := 1 / INR n.

Lemma pos_div_pos : forall eps : R, eps > 0 -> (1 / eps > 0).
Proof.
  intros eps Heps.
  apply Rlt_gt.
  unfold Rdiv.
  rewrite Rmult_1_l.
  apply Rinv_0_lt_compat.
  apply Rgt_lt in Heps.
  apply Heps.
Qed.

Lemma up_nonneg : forall eps : R, eps > 0 -> (up (1 + 1 / eps) > 0)%Z.
Proof.
  intros eps Heps.
  assert (H : 1 + 1 / eps > 0).
  {
    apply Rplus_lt_le_0_compat.
    - apply Rlt_0_1.
    - apply Rlt_le. unfold Rdiv. rewrite Rmult_comm. 
      rewrite Rmult_1_r. apply Rinv_0_lt_compat. apply Heps.
  }
  assert (H2 : IZR (up (1 + 1 / eps)) > (1 + 1 / eps) /\ IZR (up (1 + 1 / eps)) - (1 + 1 / eps) <= 1).
  {
    apply archimed.
  }
  destruct H2 as [H2 H3].
  assert (H4 : forall r1 r2 : R, r1 > r2 -> r2 < r1).
    { apply Rgt_lt. }
  assert (H5 : IZR (up (1 + 1 / eps)) > 0).
  {
    apply (Rgt_trans _ (1 + 1 / eps) _).
    - apply H2.
    - apply H.
  }
  apply lt_IZR in H5. lia.
Qed.

Lemma nat_z_relationship : forall (N : Z) (n : nat),
  (n >= Z.to_nat N)%nat -> (N <= Z.of_nat n)%Z.
Proof.
  intros N n H.
  destruct (Z_lt_le_dec N 0).
  - (* Case: N < 0 *)
    apply Z.le_trans with (m := 0%Z).
    --  lia.
    -- apply Z2Nat.inj_le; lia.
  - (* Case: N >= 0 *)
    apply Z2Nat.inj_le; lia.
Qed.

Lemma illnameitlatter : forall r1 r2 r3 : R,
  r1 >= 0 -> r2 > 0 -> r3 > 0 -> r1 >= r2 + r3 -> r1 > r3.
Proof.
  intros r1 r2 r3 H1 H2 H3 H4.
  apply Rge_gt_trans with (r2 + r3). apply H4.
  rewrite <- Rplus_0_r. rewrite Rplus_comm. apply Rplus_gt_compat_l. apply H2.
Qed.

Open Scope R_scope.

Lemma one_over_n_arbitrarily_small : arbitrarily_small one_over_n.
Proof.
  unfold arbitrarily_small. unfold one_over_n. intros eps Heps.

  set (N := (up (1 + (1 / eps)))%nat).

  exists (Z.to_nat N).

  intros n Hn.
  unfold Rabs. 
    
    destruct (Rcase_abs (1 / INR n) ) as [H | H].
    - assert (H2 : 1 / INR n >= 0).
      {
        destruct n. 
        - simpl. unfold Rdiv. rewrite Rmult_1_l. apply Req_ge. apply Rinv_0.
        - apply Rgt_ge. apply pos_div_pos.  rewrite S_INR. 
          apply Rlt_gt. apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1. 
      }
      apply Rlt_not_ge in H. contradiction.
    - assert (IZR N >= 1 + (1 / eps)).
    { 
      generalize (archimed (1 + (1 / eps))); intros [H1 H2].
      apply Rle_ge.
      - unfold N. unfold Rle. left. apply H1.
    }

    assert (INR n >= IZR N).
    {
      apply Rle_ge.
      rewrite INR_IZR_INZ.
      apply IZR_le.
      apply nat_z_relationship.
      apply Hn.
    }
    assert (INR n >= 1 + (1 / eps)).
    {
      apply Rge_trans with (r2 := IZR N).
      - apply H1.
      - apply H0.
    }
    apply Rplus_ge_compat_l with (r := 1) in H2.
    apply illnameitlatter in H2.
    -- apply Rplus_gt_reg_l in H2.
       unfold Rdiv. rewrite Rmult_1_l. apply Rgt_lt in H2. apply Rinv_lt_contravar in H2.
       --- unfold Rdiv in H2. rewrite Rmult_1_l in H2. rewrite Rinv_inv in H2. apply H2.
       --- apply Rgt_lt. apply Rmult_gt_0_compat.
           ---- apply pos_div_pos. apply Heps.
           ---- assert (H3 : 1 + 1 / eps > 0).
                { apply Rplus_lt_le_0_compat.
                  - apply Rlt_0_1.
                  - apply Rlt_le. apply pos_div_pos. apply Heps.
                }
                assert (H4 : IZR N > 0).
                { apply Rge_gt_trans with (r2 := 1 + 1 / eps).
                  - apply H0.
                  - apply H3.
                }
                apply Rge_gt_trans with (r2 := IZR N).
                { apply H1. }
                { apply H4. }
    -- apply Rle_ge. apply Rlt_le. apply Rplus_le_lt_0_compat.
      --- apply Rlt_le. apply Rlt_0_1.
      --- assert (H3 : 1 + 1 / eps > 0).
                { apply Rplus_lt_le_0_compat.
                  - apply Rlt_0_1.
                  - apply Rlt_le. apply pos_div_pos. apply Heps.
                }
                assert (H4 : IZR N > 0).
                { apply Rge_gt_trans with (r2 := 1 + 1 / eps).
                  - apply H0.
                  - apply H3.
                }
                apply Rge_gt_trans with (r2 := IZR N).
                { apply H1. }
                { apply H4. }
-- apply Rlt_gt. apply Rlt_0_1.
-- apply Rplus_lt_le_0_compat.
                  --- apply Rlt_0_1.
                  --- apply Rlt_le. apply pos_div_pos. apply Heps.
Qed.

Lemma zero_lt_ten : 0 < INR 10.
Proof.
  (* Strategy: Derive it by converting from natural numbers *)
  apply lt_INR_0.
  simpl.
  apply Nat.lt_0_succ.
Qed.

Example im_tired : exists (N : nat), 
  forall (n : nat), (n >= N)%nat -> Rabs (one_over_n n) < (1/INR 10).
Proof.
  apply one_over_n_arbitrarily_small. unfold Rdiv. apply Rlt_gt. 
  rewrite Rmult_1_l. apply Rinv_0_lt_compat. apply zero_lt_ten. 
Qed.

Lemma lim_one_over_n_0 : limit_seq one_over_n 0.
Proof.
  unfold limit_seq. intros e He.
  
  destruct (one_over_n_arbitrarily_small e He) as [N HN].
  exists N. intros n Hn.
  apply HN in Hn.
  unfold Rminus. rewrite Ropp_0. rewrite Rplus_0_r.
  apply Hn.
Qed.

Definition IQR (q : Q) : R :=
  (IZR (Qnum q)) / (IZR (Z.pos (Qden q))).

Definition fibR (n : nat) : R := IZR (fibonacci n).

Definition aR (n : nat) : R := IQR (a n).

Definition bR (n : nat) : R := IQR (b n).

Definition cR (n : nat) : R := IQR (c n).

Lemma Rmult_le : forall r1 r2 r3 r4 : R,
  (r2 > 0) -> (r4 > 0) -> r1 * r2 <= r3 * r4 -> r1 / r4 <= r3 / r2.
Proof.
  intros r1 r2 r3 r4 Hr2 Hr4 H.
  unfold Rdiv.
  apply Rmult_le_compat_r with (r := / r2) in H.
  - rewrite Rmult_assoc in H.
    rewrite Rinv_r in H.
    -- rewrite Rmult_1_r in H.
       rewrite Rmult_comm with (r1 := r3) (r2 := r4) in H.
       rewrite Rmult_assoc in H.
       apply Rmult_le_compat_r with (r := / r4) in H.
       --- rewrite Rmult_comm with (r1 := r4) (r2 := r3 * / r2) in H.
            rewrite Rmult_assoc in H.
            rewrite Rinv_r in H.
            ----- rewrite Rmult_1_r in H.
                  apply H.
            ----- apply Rgt_not_eq. apply Hr4.
      --- apply Rlt_le. apply Rinv_0_lt_compat. apply Hr4.
    -- apply Rgt_not_eq. apply Hr2.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply Hr2.
Qed.

Lemma R_ge_Q : forall q1 q2 : Q, 
  (q1 >= q2)%Q -> IQR q1 >= IQR q2.
Proof.
  intros q1 q2 H.
  unfold IQR.
  unfold Qle in H.
  apply IZR_le in H.
  rewrite mult_IZR in H.
  rewrite mult_IZR in H.
  unfold Rdiv.
  apply Rmult_le in H.
  - unfold Rdiv in H.
    apply Rle_ge in H. apply H.
  - apply Rgt_lt. apply IZR_lt. apply Pos2Z.is_pos.
  - apply Rgt_lt. apply IZR_lt. apply Pos2Z.is_pos.
Qed.

Lemma R_le_Q : forall q1 q2 : Q, 
  (q1 <= q2)%Q -> IQR q1 <= IQR q2.
Proof.
  intros q1 q2 H.
  apply Rge_le. apply R_ge_Q. apply H.
Qed.

Lemma Qseq_decreases_Rseq_decreases : forall (s : Q_seq),
  Q_seq_decreasing s -> decreasing (fun n => IQR (s n)).
Proof.
  intros s H n. unfold Q_seq_decreasing in H.
  apply R_ge_Q. apply H.
Qed.

Lemma IQR_a : decreasing (fun n => IQR (a n)).
  Proof. apply Qseq_decreases_Rseq_decreases. apply a_Q_decreasing.
Qed.

Lemma Qseq_increases_Rseq_increases : forall (s : Q_seq),
  Q_seq_increasing s -> increasing (fun n => IQR (s n)).
Proof. 
  intros s H n. unfold Q_seq_increasing in H.
  apply R_le_Q. apply H with (n := S n).

Close Scope R_scope.