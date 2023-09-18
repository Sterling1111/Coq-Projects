Require Import ZArith Lia QArith.
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
  - simpl. exfalso. apply (gt_irrefl) in H1. apply H1.
  - assert (H2: S n' = (n' + 1)%nat).
    { lia. } rewrite -> H2. rewrite <- Nat.add_assoc. simpl.
    assert (H3: (n' + 1 - 1)%nat = n').
    { lia. } rewrite -> H3.
    apply fib_suc_suc'.
Qed.

Lemma fibonacci_positive: forall n : nat, fibonacci n > 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. omega.
  - destruct n' as [| n''].
    + simpl. omega.
    + simpl. 
      assert (fibonacci n' > 0) by (apply IHn').
      assert (fibonacci (S n'') > 0) by (apply IHn').
      omega.

Lemma next_fib_greater : forall n : nat,
  fibonacci (S n) >= fibonacci n.
Proof.
  intros n. induction n as [| k IH].
  - simpl. lia.
  - induction k as [| k' IH'].
    + simpl. lia.
    + rewrite <- fib_suc_suc'. lia.
Qed.



Lemma fibonacci_positive: forall n : nat, fibonacci n > 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. lia.
  - destruct n' as [| n''].
    + simpl. lia.
    + rewrite <- Z.add_0_r at 1.
      apply Z.add_lt_mono; assumption.
Qed.

Check F.
About F.

Compute F(1) - F(5).
Compute F(3).
Compute F(5).


About Z.

Require Import Lia.

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


Theorem F_diff : forall (n : nat),
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
  intro n. rewrite <- pow_2_z. apply F_diff.
Qed.

Example F_test : F (3602) * F(3600) - F(3601)^2 = (-1)^(3600).
Proof. apply (lemma1 3600). Qed.

Compute F(15).
Compute F(20).
Compute F(25).

Require Import QArith.
Require Import Peano.

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
  - simpl. exfalso. apply (gt_irrefl) in H. apply H.
  - lia. 
Qed.

Search (_ - 0).

Require Import ZArith.

Check Z.pow_1_l.

Lemma minus_one_pow_odd : forall n : nat,
  (-1) ^ Z.of_nat (2 * n + 1) < 0.
Proof.
  intros n. induction n as [| k IH].
  - simpl. lia.
  - rewrite Nat2Z.inj_add. rewrite -> Z.pow_add_r.
    -- assert (H: (-1) ^ Z.of_nat 1 = -1). { lia. } 
       rewrite -> H. assert (H2 : (2 * S k = (2 * k + 1) + 1)%nat).
       { lia. } rewrite -> H2. rewrite Nat2Z.inj_add. rewrite -> Z.pow_add_r.
       --- rewrite -> H. rewrite <- Z.mul_assoc. assert (H3: -1 * -1 = 1).
           { lia. } rewrite -> H3. rewrite Z.mul_1_r. apply IH.
       --- lia.
       --- lia.
    -- lia.
    -- lia.
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
  - simpl. exfalso. apply (gt_irrefl) in H. apply H.
  - simpl. rewrite plus_0_r. assert (H2: (n + S n - 0)%nat = (2 * n + 1)%nat).
    { lia. } rewrite -> H2. apply minus_one_pow_odd. 
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


Lemma lemma7 : forall (n : nat),
  (n > 0)%nat -> 
  inject_Z (F ((2 * n + 2))) / inject_Z (F (2 * n + 1)) < 
  inject_Z (F (2 * n)) / inject_Z (F (2 * n - 1)).
Proof.
  intros n H1. apply lemma6 in H1. 
  assert (H2 : inject_Z (F (2 * n - 1)) * inject_Z (F (2 * n + 2)) <
             inject_Z (F (2 * n)) * inject_Z (F (2 * n + 1))).
         { repeat rewrite <- inject_Z_mul. apply inject_Z_lt. apply H1. }
  
  
  



Lemma a_decreasing_bounded_below : forall (n : nat),
  (a(n) > 0)%Z /\ (a(n+1) < a(n))%Z.
Proof.
  intros n. split.
  -  
  induction n as [| k IH].
    -- simpl. reflexivity.
    -- simpl. repeat rewrite Nat.add_0_r.
  - induction n as [| k IH].
    -- simpl. reflexivity.
    -- replace (k+1)%nat with (S k) in IH.
      --- simpl. repeat rewrite Nat.add_0_r. repeat rewrite Nat.sub_0_r.
Abort.
