Require Import Reals Lra Lia.
From Seth Require Export Complex.

Open Scope R_scope.

Lemma lemma_6_1_a : forall x : R, x <> 3 -> x^2 - 2 * x +3 <> 0.
Proof.
    intros x H1 H2. replace (x^2 - 2 * x + 3) with ((x - 1)^2 + 2) in H2 by lra.
    apply Rplus_eq_compat_r with (r := -2) in H2. rewrite Rplus_assoc in H2.
    rewrite Rplus_opp_r in H2. rewrite Rplus_0_r, Rplus_0_l in H2. pose proof (pow2_ge_0 (x - 1)) as H3. lra.
Qed.

Open Scope C_scope.

Lemma lemma_6_1_b : (forall x : C, x <> 3 -> x^2 - 2 * x + 3 <> 0) -> False.
Proof.
  intros H1. set (x := 1 + sqrt 2 * Ci). assert (H2 : x <> 3).
  { intro H2. apply c_proj_eq_inv in H2 as [H2 H3]. simpl in H2. lra. }
  assert (H3 : x^2 - 2 * x + 3 = 0).
  {
    unfold x. simpl. rewrite Cmult_1_r. apply c_proj_eq.
    replace (fst ((1 + sqrt 2 * Ci) * (1 + sqrt 2 * Ci) - 2 * (1 + sqrt 2 * Ci) + 3)) with ((- (sqrt 2 * sqrt 2) + 2)%R).
    2 : { simpl. lra. } simpl. rewrite sqrt_sqrt. lra. lra. simpl. lra.
  }
  specialize (H1 x H2 H3); auto.
Qed.

Open Scope nat_scope.

Lemma even_plus_even_nat : forall n m : nat, Nat.Even n -> Nat.Even m -> Nat.Even (n + m).
Proof. intros n m [k H1] [l H2]; exists (k + l); lia. Qed.

Lemma even_plus_odd_nat : forall n m : nat, Nat.Even n -> Nat.Odd m -> Nat.Odd (n + m).
Proof. intros n m [k H1] [l H2]; exists (k + l); lia. Qed.

Lemma even_mult_nat : forall n m : nat, Nat.Even n -> Nat.Even (n * m).
Proof. intros n m [k H1]; exists (k * m); lia. Qed.

Lemma odd_mult_odd_nat : forall n m : nat, Nat.Odd n -> Nat.Odd m -> Nat.Odd (n * m).
Proof. intros n m [k H1] [l H2]; exists (2 * k * l + k + l); lia. Qed.

Lemma lemma_6_2 : forall n : nat, 2 < n < 3 -> Nat.Odd (7 * n + 3).
Proof.
    intros n [H1 H2]. exfalso. lia.
Qed.

Open Scope Z_scope.

Lemma even_plus_even_Z : forall x y : Z, Z.Even x -> Z.Even y -> Z.Even (x + y).
Proof. intros x y [k H1] [l H2]; exists (k + l); lia. Qed.

Lemma even_plus_odd_Z : forall x y : Z, Z.Even x -> Z.Odd y -> Z.Odd (x + y).
Proof. intros x y [k H1] [l H2]; exists (k + l); lia. Qed.

Lemma odd_plus_even_Z : forall x y : Z, Z.Odd x -> Z.Even y -> Z.Odd (x + y).
Proof. intros x y H1 H2. rewrite Z.add_comm. apply even_plus_odd_Z; auto. Qed.

Lemma odd_plus_odd_Z : forall x y : Z, Z.Odd x -> Z.Odd y -> Z.Even (x + y).
Proof. intros x y [k H1] [l H2]; exists (k + l + 1); lia. Qed.

Lemma even_minus_even_Z : forall x y : Z, Z.Even x -> Z.Even y -> Z.Even (x - y).
Proof. intros x y [k H1] [l H2]; exists (k - l); lia. Qed.

Lemma even_minus_odd_Z : forall x y : Z, Z.Even x -> Z.Odd y -> Z.Odd (x - y).
Proof. intros x y [k H1] [l H2]; exists (k - l - 1); lia. Qed.

Lemma odd_minus_odd_Z : forall x y : Z, Z.Odd x -> Z.Odd y -> Z.Even (x - y).
Proof. intros x y [k H1] [l H2]; exists (k - l); lia. Qed.

Lemma odd_minus_even_Z : forall x y : Z, Z.Odd x -> Z.Even y -> Z.Odd (x - y).
Proof. intros x y [k H1] [l H2]; exists (k - l); lia. Qed.

Lemma even_mult_Z_l : forall x y : Z, Z.Even x -> Z.Even (x * y).
Proof. intros x y [k H1]; exists (k * y); lia. Qed.

Lemma even_mult_Z_r : forall x y : Z, Z.Even y -> Z.Even (x * y).
Proof. intros x y [k H1]; exists (x * k); lia. Qed.

Lemma odd_mult_odd_Z : forall x y : Z, Z.Odd x -> Z.Odd y -> Z.Odd (x * y).
Proof. intros x y [k H1] [l H2]; exists (2 * k * l + k + l); lia. Qed.

Lemma lemma_6_3 : forall x : Z, Z.Odd x -> Z.Odd (x^2).
Proof.
    intros x [k H1]; exists (2 * k * (k + 1)); lia.
Qed.

Lemma lemma_6_3_' : forall x : Z, Z.Odd x -> Z.Odd (x^2).
Proof.
    intros x H1. rewrite Z.pow_2_r. apply odd_mult_odd_Z; auto.
Qed.

Lemma lemma_6_4 : forall x : Z, Z.Even x -> Z.Odd (7 * x - 5).
Proof.
    intros x [k H1]; exists (7 * k - 3); lia. 
Qed.

Lemma lemma_6_4' : forall x : Z, Z.Even x -> Z.Odd (7 * x - 5).
Proof.
    intros x H1. apply even_minus_odd_Z.
    - apply even_mult_Z_r; auto.
    - exists 2; lia.
Qed.

Lemma lemma_6_5 : forall a b c : Z, Z.Odd a -> Z.Odd c -> Z.Even (a * b + b * c).
Proof.
    intros a b c H1 H2. pose proof Z.Even_or_Odd b as [H3 | H3].
    - apply even_plus_even_Z.
      -- apply even_mult_Z_r; auto.
      -- apply even_mult_Z_l; auto.
    - apply odd_plus_odd_Z; apply odd_mult_odd_Z; auto.
Qed.

Lemma abs_val_lt_1_Z : forall n : Z, Z.abs n < 1 -> n = 0.
Proof. intros n H1. lia. Qed.

Lemma lemma_6_6 : forall n : Z, Z.abs n < 1 -> Z.Even (3 * n - 2).
Proof.
    intros n H1. apply abs_val_lt_1_Z in H1. rewrite H1. rewrite Z.mul_0_r. exists (-1). lia.
Qed.

Lemma lemma_6_7 : forall z1 : Z, Z.Odd z1 -> exists z2 z3 : Z, z1 = z2 ^ 2 - z3 ^ 2.
Proof.
    intros z1 [k H1]; exists (k + 1), k; lia.
Qed.