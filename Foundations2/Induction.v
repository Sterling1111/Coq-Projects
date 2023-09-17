From Foundations2 Require Export Basics.

Theorem add_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intro n. simpl.
Abort.

Theorem add_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intros [| n'].
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intro n. induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_SM : forall (n m : nat),
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_comm : forall (n m : nat),
  n + m = m + n.
Proof.
  intros n m. induction n as [| k IH].
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> IH. rewrite -> plus_n_SM. reflexivity.
Qed.

Theorem add_assoc : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity. 
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Require Import Lia.

Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. rewrite -> plus_n_SM. reflexivity.
Qed.

Theorem eqb_refl : forall (n : nat),
  (n =? n) = true.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - rewrite -> IH. simpl. rewrite negb_involutive. reflexivity. 
Qed.

Theorem mult_0_plus' : forall (n m : nat),
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite -> add_comm. simpl. rewrite -> add_comm. simpl. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros. rewrite -> add_comm. 
Abort.

Theorem plus_rearrange_secondtry : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n).
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem add_shuffle3 : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> add_assoc.
  assert (H: n + m = m + n).
    { apply add_comm. }
  rewrite -> H. rewrite <- add_assoc. reflexivity.
Qed.

Lemma mul_m_Sn : forall (m n : nat),
  m * S n = m + m * n.
Proof.
  intros m n. induction m as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. rewrite -> add_shuffle3. reflexivity.
Qed.

Theorem mul_comm : forall (m n : nat),
  m * n = n * m.
Proof.
  intros m n. induction n as [| n' IHn'].
  - simpl. rewrite -> mul_0_r. reflexivity.
  - simpl. rewrite <- IHn'. rewrite -> mul_m_Sn. reflexivity. 
Qed.

Check leb.

Theorem plus_leb_compate_l : forall (n m p : nat),
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [| k IH]. 
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem leb_refl : forall (n : nat),
  (n <=? n) = true.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem zero_neqb_S : forall n : nat,
  0 =? (S n) = false.
Proof.
  intro n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intro b. destruct b as [|].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intro n. destruct n as [| n'] eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intro n. simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem all2_spec : forall (b c : bool),
  orb
    (andb b c)
    (orb (negb b)
          (negb c)) = true.
Proof.
  intros b c. destruct b as [|], c as [|].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall (n m p : nat),
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. rewrite -> add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall (n m p : nat),
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. rewrite mult_plus_distr_r. reflexivity.
Qed.

Theorem add_shuffle3' : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> add_assoc. replace (n + m) with (m + n).
  induction m as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
  - rewrite -> add_comm. reflexivity.
Qed.

Inductive bin : Type :=
| Z
| B0 (b : bin)
| B1 (b : bin).

Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 b' => B1 b'
  | B1 b' => B0 (incr b')
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Z => O
  | B0 b' => 2 * bin_to_nat b'
  | B1 b' => 2 * bin_to_nat b' + 1
  end.

Lemma double_n_plus_m : forall (n m : nat),
  double(n + m) = double n + double m.
Proof.
  intros n m. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intro b. induction b as [| b' IHb' | b' IHb'].
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. rewrite <- double_plus. rewrite -> add_comm.
    rewrite -> plus_1_l. reflexivity.
  - simpl. repeat rewrite -> add_0_r. rewrite add_comm in IHb'. 
    repeat rewrite <- double_plus. rewrite IHb'. rewrite plus_n_SM. rewrite double_n_plus_m.
    simpl. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IH.
    simpl. reflexivity.
Qed.

Theorem bin_nat_bin_fails : exists b : bin,
  nat_to_bin (bin_to_nat b) <> b.
Proof.
  exists (B0 Z). simpl. discriminate.
Qed.

Lemma double_incr : forall n : nat,
  double (S n) = S (S (double n)).
Proof.
  intro n. simpl. reflexivity.
Qed.

Definition double_bin (b : bin) : bin := 
  match b with
  | Z => Z
  | _ => B0 b
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed. 

Lemma double_incr_bin : forall b : bin,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof. 
  intros [| b' | b'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.

Compute normalize (B0 (B0 Z)).

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. rewrite -> double_incr_bin. reflexivity.
Qed.

Lemma nat_to_bin_Sn : forall n : nat,
  nat_to_bin (n + 1) = incr (nat_to_bin n).
Proof.
  intro n. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.


Theorem bin_nat_bin : forall b : bin, 
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intro b. induction b as [| b' IH | b' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> add_0_r. rewrite <- IH.
    rewrite <- double_plus. rewrite -> nat_to_bin_double. reflexivity.
  - simpl. rewrite -> add_0_r. rewrite <- double_plus. rewrite -> nat_to_bin_Sn.
    rewrite -> nat_to_bin_double. rewrite -> IH. reflexivity.  
Qed.

Compute bin_to_nat( normalize (B0 (B1 (B1 Z)))).