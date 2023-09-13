From Foundations Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat, n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n:nat, n + 0 = n.
Proof.
  intros [].
  reflexivity.
  simpl.
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem minus_n_n : forall n:nat, n - n = 0.
Proof.
  intros n.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem mul_0_r: forall(n:nat), n * 0 = 0.
Proof.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S(n+m) = n + (S m).
Proof.
  intros n m.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| k IH].
  simpl. rewrite -> add_0_r. reflexivity.
  simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  simpl. rewrite -> add_comm. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Fixpoint  double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. assumption.
Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  induction n as [|k IH].
  simpl. reflexivity.
  rewrite -> IH. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    {rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H. reflexivity.
  Qed.

Theorem add_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_assoc'' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  (*n = 0*)
  reflexivity.
  (*n = S k*)
  simpl. rewrite IH. reflexivity. 
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  assert (n + m = m + n) as H.
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H. rewrite <- add_assoc. reflexivity.
Qed.

Theorem mul_1_r : forall n : nat, n * 1 = n.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem mult_a_Sb : forall a b : nat, 

  a * S b = a + a * b.
Proof.
  intros a b.
  induction a as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite <- add_shuffle3. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  induction n as [| k IH].
  simpl. rewrite -> mul_0_r. reflexivity.
  simpl. rewrite <- IH. rewrite <- mult_a_Sb. reflexivity.
Qed.

Check leb.

Theorem plus_leb_compat_1 : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| k IH].
  simpl. rewrite -> H. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem leb_refl : forall n:nat, (n <=? n) = true.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat, 0 =? (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros [].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n : nat, (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_1 : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, 
  orb
    (andb b c)
    (orb (negb b)
          (negb c)) = true .
Proof.
  intros [][].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, 
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite <- add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, 
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc.
  replace (n + m) with (m + n).
  rewrite -> add_assoc.
  reflexivity.
  rewrite -> add_comm.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin, 
  bin_to_nat (incr b) = bin_to_nat b + 1.
Proof.
  induction b as [| k IH1 | k' IH2].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite -> add_0_r. rewrite -> add_0_r. rewrite -> IH2.
  rewrite -> add_assoc.
  assert (bin_to_nat k' + 1 + bin_to_nat k' = bin_to_nat k' + bin_to_nat k' + 1) as H.
    { rewrite <- add_assoc. replace (1 + bin_to_nat k') with (bin_to_nat k' + 1). 
      rewrite -> add_assoc. reflexivity. rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Compute bin_to_nat (B1 Z).

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IH.
  rewrite -> add_comm. rewrite -> plus_1_1. reflexivity.
Qed.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Proof.
Abort.

Lemma double_incr : forall n : nat, double (S n) = S ( S (double n)).
Proof.
  intros n.
  simpl. reflexivity.
Qed.

Compute bin_to_nat (B0 (B1 Z)).

Definition double_bin (b:bin) : bin := 
  match b with
  | Z => Z
  | B0 b' => B0 (B0 b')
  | B1 b' => B0 (B1 b')
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b, 
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros [].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Example same_bin : B0 (B0 Z) = Z.
Proof. simpl. Abort.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => B1 (normalize b')
  end.

Compute normalize (B0 (B0 Z)).
Compute normalize (B0 (B0 (B1 (B0 Z)))).

Compute bin_to_nat (B0 (B0 (B1 (B0 Z)))).

Lemma Sn_n_plus_1 : forall n, S n = n + 1.
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Lemma double_ab : forall a b : nat, double (a + b) = double a + double b.
Proof.
  intros a b.
  induction a as [| k IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Lemma double_bin_to_nat : forall b, 
  bin_to_nat b + bin_to_nat b = double (bin_to_nat b).
Proof.
  induction b as [| k IH | k IH].
  simpl. reflexivity.
  simpl. rewrite -> add_0_r. rewrite -> IH. rewrite <- double_ab. rewrite <- double_plus. reflexivity.
  simpl. rewrite -> add_0_r. rewrite -> IH. rewrite -> double_plus. rewrite -> double_plus. reflexivity.
Qed.

Lemma nat_to_bin_S_n : forall n : nat, 
  nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
  intros [].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma nat_to_bin_double_n : forall n,
  nat_to_bin (double n) = double_bin (nat_to_bin (n)).
Proof.
  induction n as [| k IH].
  simpl. reflexivity.
  rewrite -> nat_to_bin_S_n. rewrite -> double_incr_bin. rewrite <- IH. rewrite -> double_incr.
  rewrite -> nat_to_bin_S_n. rewrite -> nat_to_bin_S_n. reflexivity.
Qed.

Lemma incr_double_bin : forall b, 
  incr (double_bin b) = B1 b.
Proof.
  intros [].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b as [| k IH | k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> add_0_r. rewrite <- IH. rewrite -> double_bin_to_nat . 
    rewrite -> nat_to_bin_double_n. reflexivity.
  - simpl.  rewrite -> add_0_r. rewrite <- Sn_n_plus_1. rewrite -> nat_to_bin_S_n. 
    rewrite <- double_plus. rewrite -> nat_to_bin_double_n. rewrite -> IH.
    rewrite -> incr_double_bin. reflexivity.
Qed.