Require Import ZArith.
Open Scope Z_scope.

Fixpoint fib (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fib(n') + fib(n'')
            end
  end.

Check fib.
About fib.

Compute fib(1) - fib(5).
Compute fib(3).
Compute fib(5).


About Z.

Require Import Lia.

Lemma pow_2_z : forall (x : Z),
  x * x = Z.pow x 2.
Proof.
  intro z. unfold Z.pow. unfold Z.pow_pos. unfold Pos.iter.
  rewrite -> Z.mul_1_r. reflexivity.
Qed.

Lemma fib_suc_suc : forall n : nat, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intros n.
  destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma fib_suc_suc' : forall n : nat, fib(n+2) = fib(n+1) + fib(n).
Proof.
  intro n. 
  assert(H1: S n = (n+1)%nat).
    { lia. } rewrite <- H1.
  assert(H2: S (S n) = (n+2)%nat).
    { lia. } rewrite <- H2.
  apply fib_suc_suc.
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
  fib(n+2) * fib(n) - (fib(n+1) * fib(n+1)) = (Z.pow (-1) (Z.of_nat n)).
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - replace (fib (S k + 2)) with (fib (k+2) + fib(k + 1)).
    * rewrite -> Z.mul_add_distr_r. assert (H1: S k = (k+1)%nat).
      { rewrite -> plus_comm. simpl. reflexivity. }
    rewrite -> H1.
    assert (H2: fib ((k + 1 + 1)%nat) = fib(k+2%nat)).
      { rewrite -> Nat.add_1_r. auto. }
    rewrite -> H2.
    assert (H3: fib(k+1) * fib(k+1) = fib(k+2) * fib(k) - (-1) ^ Z.of_nat k).
      { rewrite <- IH. lia.  }
    rewrite -> H3.
    assert (H4: fib (k + 2) * fib (k + 1) +
(fib (k + 2) * fib k -
 (-1) ^ Z.of_nat k) -
fib (k + 2) * fib (k + 2) = fib(k+2) * (fib(k) + fib(k+1) - fib(k+2)) - (-1) ^ Z.of_nat k).
  { lia. }
  rewrite H4.
  assert (H5: fib k + fib (k+1) = fib(k+2)).
    { rewrite -> fib_suc_suc'. apply Z.add_comm. }
  rewrite -> H5. rewrite -> Z.sub_diag. rewrite -> Z.mul_0_r. 
  rewrite -> pow_add_one_nat. assert (H6: (-1)^1 = -1).
      { auto. } rewrite H6. lia.
    * assert(H1: (S k + 2)%nat = ((k+1) + 2)%nat).
      { lia. } rewrite H1.
      assert(H2 : fib(k+1+2) = fib(k+1+1) + fib(k+1)).
        {rewrite <- fib_suc_suc'. reflexivity. } rewrite -> H2.
      assert(H3: (k+2)%nat = (k+1+1)%nat).
        { lia. } rewrite -> H3.
      reflexivity.
Qed.


Lemma lemma1 : forall n : nat,
  fib(n+2) * fib(n) - fib(n+1) ^ 2 = (-1) ^ (Z.of_nat n).
Proof.
  intro n. rewrite <- pow_2_z. apply fib_diff.
Qed.

Example fib_fuck : fib (36) * fib(34) - fib(35)^2 = (-1)^(34).
Proof. apply (lemma1 34). Qed.

Compute fib(15).
Compute fib(20).
Compute fib(25).
Compute fib(30).
Compute fib(40).