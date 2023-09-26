Require Import Peano ZArith Lia QArith Reals Nat.

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


Lemma ge_n_ge_fib : forall n1 n2 : nat,
  (n1 >= n2)%nat -> fibonacci n1 >= fibonacci n2.
Proof.
  intros n1 n2 H.
  induction H.
  - lia.
  - assert (H2 : F (S m) >= F m).
    { apply next_fib_greater. } lia.
Qed.

Lemma bn_minus_an_ge_n : forall n : nat,
  F (n) >= Z.of_nat n.
Proof.
  intro n.
  induction n as [| k IH].
  - simpl. lia.
  - assert (H1 : (S k = k + 1)%nat).
    { lia. } rewrite H1. destruct k as [| k'] eqn: Ek.
    -- simpl. lia. 
    -- rewrite fib_suc_suc''.
       --- rewrite Nat2Z.inj_add. 
           assert (H2 : F (S k' - 1) > 0).
           { apply fibonacci_positive_strong. } lia.
           --- lia.
Qed.

Lemma fib2n_ge_fibn : forall (n : nat),
  F (2 * n) >= F n.
Proof.
  intros n. assert (H2 : (2 * n >= n)%nat).
  { lia. } apply ge_n_ge_fib in H2. apply H2.
Qed.

Lemma Zmult_ab_ge_a : forall (a b : Z),
  b > 0 -> a > 0 -> a * b >= a.
Proof.
  intros a b Hb Ha.
  replace a with (a * 1) at 2 by (apply Z.mul_1_r).
  apply Zmult_ge_compat_l.
  - lia.
  - lia.
Qed.

Lemma fib_mult_ge : forall n : nat,
  F (2 * n) * F (2 * n - 1) >= F (n).
Proof.
  intro n. assert (H1 : F (2 * n - 1) > 0).
    {apply fibonacci_positive_strong. }
  assert (H2 : F (2 * n) >= F n).
    { apply fib2n_ge_fibn. }
  assert (H3 : F (2 * n) > 0).
    { apply fibonacci_positive_strong. }
  assert (H4 : F n > 0).
    { apply fibonacci_positive_strong. }
  apply Zmult_ge_compat_r with (p := F (2 * n - 1)) in H2.
  - assert (H5 : F n * F (2 * n - 1) >= F n).
    { apply Zmult_ab_ge_a. apply H1. apply H4. }
    lia.
  - lia.
Qed.

Lemma fib_mult_ge_n : forall n : nat,
  F (2 * n) * F (2 * n - 1) >= Z.of_nat n.
Proof.
  intro n. assert (H1 : F n >= Z.of_nat n).
    { apply bn_minus_an_ge_n. }
  assert (H2 : F (2 * n) * F (2 * n - 1) >= F n).
    { apply fib_mult_ge. }
  lia.
Qed.

Open Scope R_scope.

Lemma fib_mult_ge_nR : forall n : nat,
  IZR (F (2 * n)) * IZR (F (2 * n - 1)) >= INR n.
Proof.
  intros n. rewrite <- mult_IZR. rewrite INR_IZR_INZ.
  apply IZR_ge. apply fib_mult_ge_n.
Qed.

Close Scope R_scope.

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
  forall (n : nat), a (S n) >= a n.

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

Lemma a_Q_bounded_below : Q_seq_bounded_below a.
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

Definition c (n : nat) : Q := inject_Z (F (n + 1)) / inject_Z (F n).

Definition b_minus_a (n : nat) : Q := b n - a n.

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

Lemma b_minus_a_eq : forall (n : nat), 
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

(* Define a sequence as a function from natural numbers to reals *)
Definition sequence := nat -> R.

(* Stating that a sequence is strictly decreasing *)
Definition decreasing (a : sequence) : Prop :=
  forall n : nat, a n >= a (S n).

Definition increasing (a : sequence) : Prop :=
  forall n : nat, a n <= a (S n).

(* Stating that a sequence is bounded below *)
Definition bounded_below (a : sequence) : Prop :=
  exists LB : R, forall n : nat, LB <= a n.

Definition bounded_above (a : sequence) : Prop := 
  exists UB : R, forall n : nat, UB >= a n.

Definition convergent_sequence (a : sequence) : Prop :=
  exists (L : R), 
    forall (eps : R), eps > 0 ->
      exists (N : nat), forall (n : nat), (n >= N)%nat -> Rabs (a n - L) < eps.

Definition limit_of_sequence (a : nat -> R) (L : R) : Prop :=
  forall eps : R, eps > 0 ->
                  exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (a n - L) < eps.

Definition arbitrarily_small (a : sequence) : Prop :=
  limit_of_sequence a 0.

Definition monotonic_sequence (a : sequence) : Prop :=
  (increasing a /\ bounded_above a) \/ (decreasing a /\ bounded_below a).

(* Monotonic Sequence Theorem for strictly decreasing sequences *)
Axiom Monotonic_Sequence_Theorem :
  forall (a : sequence), monotonic_sequence a -> convergent_sequence a.

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
  unfold arbitrarily_small. unfold limit_of_sequence. intros eps H1. unfold one_over_n.

  set (N := (up (1 + (1 / eps)))%nat).

  exists (Z.to_nat N).

  intros n H2. unfold Rabs. rewrite Rminus_0_r.
  
  destruct (Rcase_abs (1 / INR n) ) as [H3 | H3].
    - assert (H4 : 1 / INR n >= 0).
      {
        destruct n. 
        - simpl. unfold Rdiv. rewrite Rmult_1_l. apply Req_ge. apply Rinv_0.
        - apply Rgt_ge. apply pos_div_pos.  rewrite S_INR. 
          apply Rlt_gt. apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1. 
      }
      apply Rlt_not_ge in H4. contradiction. apply H3.
    - assert (H4 : IZR N >= 1 + (1 / eps)).
    { 
      generalize (archimed (1 + (1 / eps))). intros [H4 H5].
      apply Rle_ge.
      - unfold N. unfold Rle. left. apply H4.
    }

    assert (H5 : INR n >= IZR N).
    {
      apply Rle_ge.
      rewrite INR_IZR_INZ.
      apply IZR_le.
      apply nat_z_relationship.
      apply H2.
    }
    assert (H6 : INR n >= 1 + (1 / eps)).
    {
      apply Rge_trans with (r2 := IZR N).
      - apply H5.
      - apply H4.
    }
    assert (H7 : 1 + 1 / eps > 0).
    {
      apply Rplus_lt_le_0_compat.
      - apply Rlt_0_1.
      - apply Rlt_le. apply pos_div_pos. apply H1.
    }
    assert (H8 : IZR N > 0).
    {
      apply Rge_gt_trans with (r2 := 1 + 1 / eps).
      - apply H4.
      - apply H7.
    }
    pose proof H6 as H9.
    apply Rplus_ge_compat_l with (r := 1) in H6.
    apply illnameitlatter in H6.
    -- apply Rplus_gt_reg_l in H6.
       unfold Rdiv. rewrite Rmult_1_l. apply Rgt_lt in H6. apply Rinv_lt_contravar in H6.
       --- unfold Rdiv in H6. rewrite Rmult_1_l in H6. rewrite Rinv_inv in H6. apply H6.
       --- apply Rgt_lt. apply Rmult_gt_0_compat.
           ---- apply pos_div_pos. apply H1.
           ---- apply Rge_gt_trans with (r2 := IZR N).
                { apply H5. }
                { apply H8. }
    -- apply Rle_ge. apply Rlt_le. apply Rplus_le_lt_0_compat.
      --- apply Rlt_le. apply Rlt_0_1.
      --- apply Rge_gt_trans with (r2 := IZR N).
          { apply H5. }
          { apply H8. }
    -- apply Rlt_gt. apply Rlt_0_1.
    -- apply Rplus_lt_le_0_compat.
      --- apply Rlt_0_1.
      --- apply Rlt_le. apply pos_div_pos. apply H1.
Qed.

Lemma zero_lt_ten : 0 < INR 10.
Proof.
  (* Strategy: Derive it by converting from natural numbers *)
  apply lt_INR_0.
  simpl.
  apply Nat.lt_0_succ.
Qed.

Lemma lim_one_over_n_0 : limit_of_sequence one_over_n 0.
Proof.
  apply one_over_n_arbitrarily_small.
Qed.

Example im_tired : exists (N : nat), 
  forall (n : nat), (n >= N)%nat -> Rabs (one_over_n n - 0) < (1/INR 10).
Proof.
  apply lim_one_over_n_0.
  apply pos_div_pos.
  apply zero_lt_ten.
Qed.

Definition IQR (q : Q) : R :=
  (IZR (Qnum q)) / (IZR (Z.pos (Qden q))).

Definition fibR (n : nat) : R := IZR (fibonacci n).

Definition aR (n : nat) : R := IQR (a n).

Definition bR (n : nat) : R := IQR (b n).

Definition b_minus_aR (n : nat) : R := IQR (b_minus_a n).

Definition cR (n : nat) : R := IQR (c n).

Open Scope Z_scope.

Compute Qnum (1 # 2).

Lemma Z_gt_0_implies_Zpos : forall z2 : Z,
  z2 > 0 -> z2 = Zpos (Z.to_pos z2).
Proof.
  intros z2 H.

  (* Use the Z2Pos.id function which provides the identity between positive numbers and their Z counterpart *)
  symmetry. 
  apply Z2Pos.id.
  lia.
Qed.

Lemma Qnum_extract: forall z1 z2 : Z,
  z2 > 0 -> Qnum (inject_Z z1 / inject_Z z2) = z1.
Proof.
  intros z1 z2 H.
  rewrite Z_gt_0_implies_Zpos with (z2 := z2).
  - simpl. lia.
  - lia.
Qed.

Lemma Qden_extract: forall z1 z2 : Z,
  z2 > 0 -> Qden (inject_Z z1 / inject_Z z2) = Z.to_pos z2.
Proof.
  intros z1 z2 H.
  rewrite Z_gt_0_implies_Zpos with (z2 := z2).
  - simpl. lia.
  - lia.
Qed.

Lemma Qnum_value : forall n : nat, 
  Qnum ((-1)%Q / inject_Z (F (2 * n) * F (2 * n - 1))) = -1.
Proof.
  intros n.
  replace (-1)%Q with (inject_Z ((-1)%Z)) by reflexivity.
  rewrite Qnum_extract with (z2 := (F (2 * n) * F (2 * n - 1))%Z).
  - reflexivity.
  - assert (H : (F (2 * n) > 0)%Z).
    { apply fibonacci_positive_strong. }
    assert (H2 : (F (2 * n - 1) > 0)%Z).
    { apply fibonacci_positive_strong. }
    lia.
Qed.

Lemma Qden_value : forall n : nat, 
  Qden ((-1)%Q / inject_Z (F (2 * n) * F (2 * n - 1))) = Z.to_pos (F (2 * n) * F (2 * n - 1)).
Proof.
  intros n.
  replace (-1)%Q with (inject_Z ((-1)%Z)) by reflexivity.
  rewrite Qden_extract with (z2 := (F (2 * n) * F (2 * n - 1))%Z).
  - reflexivity.
  - assert (H : (F (2 * n) > 0)%Z).
    { apply fibonacci_positive_strong. }
    assert (H2 : (F (2 * n - 1) > 0)%Z).
    { apply fibonacci_positive_strong. }
    lia.
Qed.

Close Scope Z_scope.

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

Lemma div_standard_lib : forall r:R, r <> 0 -> / r = 1 / r.
Proof.
  intros r Hr.
  unfold Rdiv.
  rewrite Rmult_1_l. reflexivity.
Qed.

Lemma Rmult_lt : forall r1 r2 r3 r4 : R,
  (r2 > 0) -> (r4 > 0) -> r1 * r2 < r3 * r4 -> r1 / r4 < r3 / r2.
Proof.
  intros r1 r2 r3 r4 Hr2 Hr4 H.
  unfold Rdiv.
  apply Rmult_lt_compat_r with (r := / r2) in H.
  - rewrite Rmult_assoc in H.
    rewrite Rinv_r in H.
    -- rewrite Rmult_1_r in H.
       rewrite Rmult_comm with (r1 := r3) (r2 := r4) in H.
       rewrite Rmult_assoc in H.
       apply Rmult_lt_compat_r with (r := / r4) in H.
       --- rewrite Rmult_comm with (r1 := r4) (r2 := r3 * / r2) in H.
            rewrite Rmult_assoc in H.
            rewrite Rinv_r in H.
            ----- rewrite Rmult_1_r in H.
                  apply H.
            ----- apply Rgt_not_eq. apply Hr4.
      --- apply Rgt_lt. rewrite div_standard_lib. apply pos_div_pos. apply Hr4.
          apply Rgt_not_eq. apply Hr4.
    -- apply Rgt_not_eq. apply Hr2.
  - apply Rlt_gt. rewrite div_standard_lib. apply pos_div_pos. apply Hr2.
    apply Rgt_not_eq. apply Hr2.
Qed.

Lemma R_gt_Q : forall q1 q2 : Q, 
  (q1 > q2)%Q -> IQR q1 > IQR q2.
Proof.
  intros q1 q2 H.
  unfold IQR.
  unfold Qlt in H.
  apply IZR_lt in H.
  rewrite mult_IZR in H.
  rewrite mult_IZR in H.
  unfold Rdiv.
  apply Rmult_lt in H.
  - unfold Rdiv in H.
    apply Rlt_gt. apply H.
  - apply Rgt_lt. apply IZR_lt. apply Pos2Z.is_pos.
  - apply Rgt_lt. apply IZR_lt. apply Pos2Z.is_pos.
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

Lemma R_lt_Q : forall q1 q2 : Q, 
  (q1 < q2)%Q -> IQR q1 < IQR q2.
Proof.
  intros q1 q2 H. apply R_gt_Q. apply H.
Qed.

Lemma b_minus_aR_eq : forall (n : nat), 
  b_minus_aR n = -1 / (fibR (2*n) * fibR (2*n - 1)).
Proof.
  intros n. unfold b_minus_aR. unfold b_minus_a. unfold fibR.
  rewrite b_minus_a_eq. rewrite <- mult_IZR. rewrite <- inject_Z_mult.
  unfold IQR. rewrite Qnum_value. 
  replace (-1)%Q with (inject_Z (-1)%Z) by reflexivity.
  rewrite Qden_value. rewrite <- Z_gt_0_implies_Zpos. reflexivity.
  assert (H : (F (2 * n) > 0)%Z).
  { apply fibonacci_positive_strong. }
  assert (H2 : (F (2 * n - 1) > 0)%Z).
  { apply fibonacci_positive_strong. }
  lia.
Qed.

Lemma b_minus_a_neg : forall (n : nat),
  (b_minus_a n < 0)%Q.
Proof.
  intro n.
  unfold b_minus_a.
  rewrite b_minus_a_eq.
  assert (H : (fibonacci (2 * n) > 0)%Z).
  { apply fibonacci_positive_strong. }
  assert (H2 : (fibonacci (2 * n - 1) > 0)%Z).
  { apply fibonacci_positive_strong. }
  unfold Qlt.
  rewrite <- inject_Z_mult.
  rewrite Qnum_value. rewrite Qden_value. simpl. lia.
Qed.

Lemma Q_neg_Z_neg : forall q : Q,
  (q < 0)%Q -> IQR q < 0.
Proof.
  intros q H.
  assert (IQR 0 = 0).
  {
    unfold IQR.
    simpl. unfold Rdiv. rewrite Rmult_0_l. reflexivity.
  } rewrite <- H0. apply R_gt_Q. apply H.
Qed.

Lemma b_minus_aR_neg : forall (n : nat),
  b_minus_aR n < 0.
Proof.
  intro n. unfold b_minus_aR. unfold b_minus_a.
  assert (H1 : (b n - a n < 0)%Q).
  { apply b_minus_a_neg. }
  apply Q_neg_Z_neg. apply H1.
Qed.

Lemma one_over_nR_pos : forall (n : nat),
  one_over_n n >= 0.
Proof.
  unfold one_over_n. destruct n. 
  - simpl. unfold Rdiv. rewrite Rmult_1_l. apply Req_ge. apply Rinv_0.
  - apply Rgt_ge. apply pos_div_pos.  rewrite S_INR. 
  apply Rlt_gt. apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
Qed. 

Lemma double_negation : - (-1) = 1.
Proof.
  (* Use the definition of -1 *)
  rewrite <- Ropp_involutive.
  reflexivity.
Qed.

Lemma div_r1_le_div_r2 : forall r1 r2 : R,
  (r1 > 0) -> (r1 <= r2) -> (/ r1 >= / r2).
Proof.
  intros r1 r2 Hr1 Hr2.
  apply Rle_ge. apply Rinv_le_contravar. 
  - apply Rgt_lt in Hr1. assert (H : r2 > 0).
    { apply Rlt_le_trans with (r2 := r1). apply Hr1. apply Hr2. }
    apply Hr1.
  - apply Hr2. 
Qed.    

Lemma INR_n_gt_0 : forall n : nat, (n >= 1)%nat -> INR n > 0.
Proof.
  intros n H.
  induction H.
  - simpl. apply Rlt_0_1.
  - rewrite S_INR. apply Rplus_le_lt_0_compat.
    -- apply Rlt_le. apply IHle.
    -- apply Rlt_0_1.
Qed.

Lemma b_minus_aR_lte_one_over_n : forall (n : nat),
  (n >= 1)%nat -> - b_minus_aR n <= one_over_n n.
Proof.
  intros n H. unfold b_minus_aR. unfold one_over_n. unfold b_minus_a.
  rewrite b_minus_a_eq. rewrite <- inject_Z_mult. unfold IQR. rewrite Qnum_value.
  rewrite Qden_value. rewrite <- Z_gt_0_implies_Zpos.
  - unfold Rdiv. rewrite Ropp_mult_distr_l. rewrite double_negation.
    repeat rewrite Rmult_1_l. apply Rge_le. apply div_r1_le_div_r2.
    -- apply INR_n_gt_0. apply H.
    -- apply Rge_le. rewrite mult_IZR. apply fib_mult_ge_nR.
  - assert (H2 : (F (2 * n) > 0)%Z).
    { apply fibonacci_positive_strong. }
    assert (H3 : (F (2 * n - 1) > 0)%Z).
    { apply fibonacci_positive_strong. }
    lia.
Qed.

Lemma b_minus_aR_le_mag_one_over_n : forall (n : nat),
  (n >= 1)%nat -> Rabs(b_minus_aR n - 0) <= Rabs(one_over_n n - 0).
Proof.
  intros n H. repeat rewrite Rminus_0_r. unfold Rabs.
  assert (H1 : b_minus_aR n < 0).
    { apply b_minus_aR_neg. }
  assert (H2 : one_over_n n >= 0).
    { apply one_over_nR_pos. }
  destruct (Rcase_abs (b_minus_aR n)) as [H3 | H4].
  - destruct (Rcase_abs (one_over_n n)) as [H4 | H5].
    -- apply (Rlt_not_ge _ _ H4) in H2. contradiction.
    -- apply b_minus_aR_lte_one_over_n. apply H.
  - destruct (Rcase_abs (one_over_n n)) as [H5 | H6].
    -- apply (Rlt_not_ge _ _ H5) in H2. contradiction.
    -- apply (Rlt_not_ge _ _ H1) in H4. contradiction.
Qed.

Lemma b_minus_aR_arbitrarily_small : arbitrarily_small b_minus_aR.
Proof.
  unfold arbitrarily_small. unfold limit_of_sequence. intros eps H1.
  assert (H2 : exists N, forall n, (n >= N)%nat -> Rabs (one_over_n n - 0) < eps).
  { apply one_over_n_arbitrarily_small. apply H1. }
  destruct H2 as [N HN].

  exists ((N + 1)%nat). intros n Hn_ge_N.
  apply Rle_lt_trans with (r2 := Rabs (one_over_n n - 0)).
  - apply b_minus_aR_le_mag_one_over_n. lia.
  - apply HN. lia.
Qed.

Lemma lim_b_minus_aR_0 : limit_of_sequence b_minus_aR 0.
Proof.
  apply b_minus_aR_arbitrarily_small.
Qed.

Lemma Qseq_decreases_Rseq_decreases : forall (a : Q_seq),
  Q_seq_decreasing a -> decreasing (fun n => IQR (a n)).
Proof.
  intros a H n. unfold Q_seq_decreasing in H.
  apply R_ge_Q. apply H.
Qed.

Lemma IQR_a : decreasing (fun n => IQR (a n)).
  Proof. apply Qseq_decreases_Rseq_decreases. apply a_Q_decreasing.
Qed.

Lemma Qseq_increases_Rseq_increases : forall (a : Q_seq),
  Q_seq_increasing a -> increasing (fun n => IQR (a n)).
Proof. 
  intros a H n. unfold Q_seq_increasing in H.
  apply R_le_Q. apply H.
Qed.

Lemma Q_seq_bounded_above_R_seq_bounded_above : forall (a : Q_seq),
  Q_seq_bounded_above a -> bounded_above (fun n => IQR (a n)).
Proof.
  intros a H. unfold Q_seq_bounded_above in H.
  unfold bounded_above. destruct H as [UB H].
  exists (IQR UB). intros n. apply R_ge_Q. apply H.
Qed.

Lemma Q_seq_bounded_below_R_seq_bounded_below : forall (a : Q_seq),
  Q_seq_bounded_below a -> bounded_below (fun n => IQR (a n)).
Proof. 
  intros a H. unfold Q_seq_bounded_below in H.
  unfold bounded_below. destruct H as [LB H].
  exists (IQR LB). intros n. apply R_le_Q. apply H.
Qed.

Lemma IQR_a_bounded_below : bounded_below (fun n => IQR (a n)).
  Proof. apply Q_seq_bounded_below_R_seq_bounded_below. apply a_Q_bounded_below.
Qed.

Lemma IQR_b_bounded_above : bounded_above (fun n => IQR (b n)).
  Proof. apply Q_seq_bounded_above_R_seq_bounded_above. apply b_Q_bounded_above.
Qed.

Lemma aR_monotonic_sequence : monotonic_sequence aR.
Proof.
  unfold monotonic_sequence. right. split.
  - apply Qseq_decreases_Rseq_decreases. apply a_Q_decreasing.
  - apply Q_seq_bounded_below_R_seq_bounded_below. apply a_Q_bounded_below.
Qed.

Lemma bR_monotonic_sequence : monotonic_sequence bR.
Proof.
  unfold monotonic_sequence. left. split.
  - apply Qseq_increases_Rseq_increases. apply b_Q_increasing.
  - apply Q_seq_bounded_above_R_seq_bounded_above. apply b_Q_bounded_above.
Qed.

Lemma bR_converges : convergent_sequence bR.
Proof.
  apply Monotonic_Sequence_Theorem. apply bR_monotonic_sequence.
Qed.

Lemma aR_converges : convergent_sequence aR.
Proof.
  apply Monotonic_Sequence_Theorem. apply aR_monotonic_sequence.
Qed.

Require Import Lra.

Lemma Rabs_triang_3 : forall r1 r2 r3 : R,
  Rabs (r1 + r2 + r3) <= Rabs r1 + Rabs r2 + Rabs r3.
Proof.
  intros r1 r2 r3.

  assert (H1 : Rabs (r1 + r2) <= Rabs(r1) + Rabs(r2)) by apply Rabs_triang.
  assert (H2 : Rabs (r1 + r2 + r3) <= Rabs(r1 + r2) + Rabs(r3)) by apply Rabs_triang.
  apply Rplus_le_compat_r with (r := Rabs r3) in H1.
  apply Rle_trans with (r2 := Rabs (r1 + r2) + Rabs r3).
  - apply H2.
  - apply H1.
Qed.

Lemma two_seq_converge_to_same_limit: 
  forall (a b : sequence) (La Lb : R),
  (* Assuming a_n converges to La and b_n converges to Lb *)
  limit_of_sequence a La -> limit_of_sequence b Lb -> arbitrarily_small (fun n => b n - a n) ->
  La = Lb.
Proof.
  intros a b La Lb Ha Hb Hdiff.

  unfold limit_of_sequence in Ha, Hb.
  unfold arbitrarily_small in Hdiff. 
  unfold limit_of_sequence in Hdiff.

  pose (eps := Rabs (La - Lb)).
  pose proof (Rtotal_order La Lb) as [Hlt|[Heq|Hgt]].

  - assert (Heps_pos : eps > 0).
    { unfold eps. apply Rabs_pos_lt. lra. }
    assert (Heps_div_4_pos : eps / 4 > 0).
    { apply Rlt_gt. apply Rmult_lt_0_compat. apply Heps_pos. apply Rinv_0_lt_compat. lra. }
      
    destruct (Ha (eps / 4) Heps_div_4_pos) as [Na HNa].
    destruct (Hb (eps / 4) Heps_div_4_pos) as [Nb HNb].
    destruct (Hdiff (eps / 4) Heps_div_4_pos) as [Nc HNc].

    pose (N := max (max Na Nb) Nc).
    pose (n := N).

    assert (Hna : (n >= Na)%nat). lia.
    assert (Hnb : (n >= Nb)%nat). lia.
    assert (Hnc : (n >= Nc)%nat). lia.
    assert (Hnaeps : ((eps / 4) > Rabs (a n - La))). { apply HNa. apply Hna. }
    assert (Hnbeps : ((eps / 4) > Rabs (b n - Lb))). { apply HNb. apply Hnb. }
    assert (Hndeps : ((eps / 4) > Rabs (b n - a n))). { rewrite <- Rminus_0_r with (r := b n - a n). apply HNc. apply Hnc. }
    assert (Heps_eq : eps = Rabs((La - a n) + (b n - Lb) + (a n - b n))).
    { unfold eps. assert ((La - a n) + (b n - Lb) + (a n - b n) = La - Lb) by lra. rewrite H. reflexivity. }
    assert (Heps_lte : eps <= Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Heps_eq. apply Rabs_triang_3. }
    assert (Heps_lte_eq : Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n) = Rabs (a n - La) + Rabs (b n - Lb) + Rabs (b n - a n)).
    { rewrite Rabs_minus_sym. rewrite Rabs_minus_sym with (x := a n) (y := b n). reflexivity. }

    rewrite Heps_lte_eq in Heps_lte.
    assert (Heps_lte_lt : Rabs (a n - La) + Rabs (Lb - b n) + Rabs (b n - a n) < (eps / 4) + (eps / 4) + (eps / 4)) by lra.
    replace (eps / 4 + eps / 4 + eps / 4) with (3 * eps / 4) in Heps_lte_lt by lra.
    assert (H_contra : eps < 3 * eps / 4) by lra. lra.

  - assumption.

  - assert (Heps_pos : eps > 0).
    { unfold eps. apply Rabs_pos_lt. lra. }
    assert (Heps_div_4_pos : eps / 4 > 0).
    { apply Rlt_gt. apply Rmult_lt_0_compat. apply Heps_pos. apply Rinv_0_lt_compat. lra. }
      
    destruct (Ha (eps / 4) Heps_div_4_pos) as [Na HNa].
    destruct (Hb (eps / 4) Heps_div_4_pos) as [Nb HNb].
    destruct (Hdiff (eps / 4) Heps_div_4_pos) as [Nc HNc].

    pose (N := max (max Na Nb) Nc).
    pose (n := N).

    assert (Hna : (n >= Na)%nat). lia.
    assert (Hnb : (n >= Nb)%nat). lia.
    assert (Hnc : (n >= Nc)%nat). lia.
    assert (Hnaeps : ((eps / 4) > Rabs (a n - La))). { apply HNa. apply Hna. }
    assert (Hnbeps : ((eps / 4) > Rabs (b n - Lb))). { apply HNb. apply Hnb. }
    assert (Hndeps : ((eps / 4) > Rabs (b n - a n))). { rewrite <- Rminus_0_r with (r := b n - a n). apply HNc. apply Hnc. }
    assert (Heps_eq : eps = Rabs((La - a n) + (b n - Lb) + (a n - b n))).
    { unfold eps. assert ((La - a n) + (b n - Lb) + (a n - b n) = La - Lb) by lra. rewrite H. reflexivity. }
    assert (Heps_lte : eps <= Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n)).
    { rewrite Heps_eq. apply Rabs_triang_3. }
    assert (Heps_lte_eq : Rabs (La - a n) + Rabs (b n - Lb) + Rabs (a n - b n) = Rabs (a n - La) + Rabs (b n - Lb) + Rabs (b n - a n)).
    { rewrite Rabs_minus_sym. rewrite Rabs_minus_sym with (x := a n) (y := b n). reflexivity. }

    rewrite Heps_lte_eq in Heps_lte.
    assert (Heps_lte_lt : Rabs (a n - La) + Rabs (Lb - b n) + Rabs (b n - a n) < (eps / 4) + (eps / 4) + (eps / 4)) by lra.
    replace (eps / 4 + eps / 4 + eps / 4) with (3 * eps / 4) in Heps_lte_lt by lra.
    assert (H_contra : eps < 3 * eps / 4) by lra. lra.
Qed.

Open Scope Z_scope.
Lemma Zpos_distrib_mult : forall p q : positive, 
  Z.pos (p * q) = Z.pos p * Z.pos q.
Proof.
  intros. reflexivity.
Qed.
Close Scope Z_scope.

Lemma IQR_minus : forall q1 q2 : Q,
  IQR (q1 - q2) = IQR q1 - IQR q2.
Proof.
  intros q1 q2.
  unfold IQR.
  destruct q1 as [q1n q1d].
  destruct q2 as [q2n q2d].
  simpl. rewrite Zpos_distrib_mult.
  rewrite mult_IZR.

  assert (IZR q1n / IZR (Z.pos q1d) - IZR q2n / IZR (Z.pos q2d) = (IZR q1n * IZR (Z.pos q2d) - IZR q2n * IZR (Z.pos q1d)) / (IZR (Z.pos q1d) * IZR (Z.pos q2d))).
  { field. split.
    - intros contra. assert( (Z.pos q2d > 0)%Z) by lia. apply eq_IZR_R0 in contra. lia.
    - assert( (Z.pos q2d > 0)%Z) by lia. intros contra. apply eq_IZR_R0 in contra. lia.
  } rewrite H.

  clear H.

  assert ((q1n * Z.pos q2d + - q2n * Z.pos q1d = q1n * Z.pos q2d - q2n * Z.pos q1d)%Z) by lia.

  rewrite H. clear H.

  rewrite minus_IZR.
  rewrite mult_IZR. rewrite mult_IZR. reflexivity.
Qed.

Require Import FunctionalExtensionality.

Lemma aR_bR_same_limit : forall La Lb : R,
  (limit_of_sequence aR La /\ limit_of_sequence bR Lb) -> (La = Lb).
Proof.
  intros La Lb [H1 H2].
  apply two_seq_converge_to_same_limit with (a := aR) (b := bR).
  - apply H1.
  - apply H2.
  - unfold arbitrarily_small. replace (fun n : nat => bR n - aR n) with (b_minus_aR).
    -- apply lim_b_minus_aR_0.
    -- unfold b_minus_aR. unfold bR. unfold aR. unfold b_minus_a. apply functional_extensionality. intros n. rewrite IQR_minus. reflexivity.
Qed.

Lemma odd_div_2 :
  forall n m, Nat.Odd n -> n = (2 * m + 1)%nat -> (n / 2 = m)%nat.
Proof.
  intros n m Hodd Heq.
  
  destruct Hodd as [m' Hm'].

  assert (m = m') as Hm_m' by lia.
  subst m'.

  rewrite Heq. rewrite Nat.add_comm. rewrite Nat.mul_comm.
  rewrite Nat.div_add.
  - simpl. reflexivity.
  - lia.
Qed.

Lemma even_div_2 : forall n m, Nat.Even n -> n = (2 * m)%nat -> (n / 2 = m)%nat.
Proof.
  intros n m Heven Heq.
  rewrite Heq.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  - reflexivity.
  - lia.
Qed.

Lemma n_odd_cR_eq_aR : forall (n : nat),
  Nat.Odd n -> cR n = aR ((n / 2 + 1)%nat).
Proof.
  intros n H1. unfold cR. unfold aR. unfold c. unfold a.
  destruct n as [| n'] eqn:En.
  - inversion H1. lia.
  - pose proof H1 as H2. destruct H1 as [k H1].
    assert ((S n' / 2 = k)%nat).
    { apply odd_div_2. apply H2. apply H1. }
    assert ((S n' / 2 + 1 = k + 1)%nat) by lia.
    destruct ((S n' / 2 + 1)%nat).
    -- lia.
    -- rewrite H1. rewrite H0. replace ((2 * (k + 1))%nat) with  ((2 * k + 1 + 1)%nat) by lia.
       replace ((2 * k + 1 + 1 - 1)%nat) with ((2 * k + 1)%nat) by lia. reflexivity. 
Qed.

Lemma n_even_cR_eq_bR : forall (n : nat),
  Nat.Even n -> cR n = bR ((n / 2)%nat).
Proof.
  intros n H1. unfold cR. unfold bR. unfold c. unfold b.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - pose proof H1 as H2. destruct H1 as [k H1].
    assert ((S n' / 2 = k)%nat).
    { apply even_div_2. apply H2. apply H1. }
    assert ((S n' / 2 = k)%nat) by lia.
    rewrite H. rewrite H1. replace ((2 * k)%nat) with  ((2 * k + 1 - 1)%nat) by lia.
    replace ((2 * k + 1 - 1)%nat) with ((2 * k)%nat) by lia. reflexivity.
Qed.

Lemma c_converges_to_L:
  forall (a b c : sequence) (L : R),
  limit_of_sequence a L ->
  limit_of_sequence b L ->
  (forall n : nat,
    (Nat.Even n -> c n = b ((n / 2)%nat)) /\
    (Nat.Odd n -> c n = a ((n / 2 + 1)%nat))) ->
  limit_of_sequence c L.
Proof.
intros a b c L Han Hbn Hcn.

unfold limit_of_sequence in Han, Hbn. unfold limit_of_sequence.
intros eps Heps.

destruct (Han eps Heps) as [Na HNa].
destruct (Hbn eps Heps) as [Nb HNb].

set(N := max (2 * Na - 1) (2 * Nb)).
exists N.

intros n Hn.

destruct (Hcn n) as [Heven1 Hodd1].

destruct (Nat.Even_or_Odd n) as [Heven2 | Hodd2].
- pose proof Heven2 as Heven3. apply Heven1 in Heven2.
  rewrite Heven2. apply HNb. destruct (Heven3) as [k H]. assert ((n / 2 = k)%nat).
  { apply even_div_2. apply Heven3. apply H. } lia.
- pose proof Hodd2 as Hodd3. apply Hodd1 in Hodd2.
  rewrite Hodd2. apply HNa. destruct (Hodd3) as [k H]. assert ((n / 2 = k)%nat).
  { apply odd_div_2. apply Hodd3. apply H. } lia.
Qed.

Theorem cR_has_limit : forall (L1 L2: R),
  limit_of_sequence aR L1 ->
  limit_of_sequence bR L2 ->
  (limit_of_sequence cR L1 /\ limit_of_sequence cR L2).
Proof.
  intros L1 L2 H1 H2.

  assert (H4 : L1 = L2).
  { apply aR_bR_same_limit. split; assumption. }

  split.

  - apply c_converges_to_L with (a := aR) (b := bR).
    -- apply H1.
    -- rewrite <- H4 in H2. apply H2.
    -- intros n. split; intros Hparity.
      --- apply n_even_cR_eq_bR. apply Hparity.
      --- apply n_odd_cR_eq_aR. apply Hparity.
  - apply c_converges_to_L with (a := aR) (b := bR).
    -- rewrite H4 in H1. apply H1.
    -- apply H2.
    -- intros n. split; intros Hparity.
      --- apply n_even_cR_eq_bR. apply Hparity.
      --- apply n_odd_cR_eq_aR. apply Hparity.
Qed.

Theorem cR_convergent : convergent_sequence cR.
Proof.
  assert (HaR : convergent_sequence aR) by apply aR_converges.
  assert (HbR : convergent_sequence bR) by apply bR_converges.

  destruct HaR as [La Ha], HbR as [Lb Hb].

  assert (HcR_both : limit_of_sequence cR La /\ limit_of_sequence cR Lb).
  { apply cR_has_limit; assumption. }

  destruct HcR_both as [HcR1 HcR2].
  unfold convergent_sequence. exists Lb. assumption.
Qed.

Close Scope R_scope.