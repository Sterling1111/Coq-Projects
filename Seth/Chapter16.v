Require Import ZArith Lia Classical Reals Lra Classical_sets List
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image.
From Seth Require Export Chapter15.
From Seth Require Import Fibonacci Sums Sets Binomial.
Import ListNotations SetNotations Choose_Notations.

Open Scope nat_scope.

Lemma lemma_16_1_a : forall n,
  n ∁ 0 = 1 /\ n ∁ n = 1.
Proof.
  split. 
  - apply n_choose_0.
  - apply n_choose_n.
Qed.

Lemma lemma_16_1_b : forall n,
  n > 0 -> n ∁ 1 = n /\ n ∁ (n - 1) = n.
Proof.
  intros n H1. split.
  - apply n_choose_1.
  - replace n with (S (n - 1)) at 1 by lia. rewrite Sn_choose_n. lia.
Qed.

Ltac choose_cases n k H1 H2 :=
  assert (n = k \/ n > k) as [H1 | H1]; assert (k = 0 \/ k > 0) as [H2 | H2] by lia; 
  subst; try rewrite Nat.sub_0_r in *; simpl; try lia.

Lemma lemma_16_2 : forall n k,
  n >= k -> n ∁ k = n ∁ (n - k).
Proof.
  intros n k H1. repeat rewrite n_choose_k_def; try lia.
  replace (n - (n - k)) with k by lia. rewrite Nat.mul_comm. reflexivity.
Qed.

Lemma lemma_16_3 : forall n j k,
  n >= j -> n >= k -> n ∁ j * (n - j) ∁ k = n ∁ k * (n - k) ∁ j.
Proof.
  intros n j k H1 H2. assert (n - k < j \/ n - k >= j) as [H3 | H3] by lia.
  - rewrite n_lt_k_choose_k with (n := n - j) (k := k); try lia. rewrite Nat.mul_0_r.
    rewrite n_lt_k_choose_k with (n := (n - k)) (k := j); try lia.
  - repeat rewrite n_choose_k_def; try lia. pose proof fact_div (n - j) k ltac : (lia) as [p H4].
    pose proof fact_div (n - k) j ltac : (lia) as [q H5].  pose proof fact_div n k ltac : (lia) as [r H6].
    pose proof fact_div n j ltac : (lia) as [s H7].

    pose proof (fact_neq_0) as Hfact.

    replace (fact n / (fact j * fact (n - j)) * (fact (n - j) / (fact k * fact (n - j - k)))) with 
            (fact n / (fact j * fact (n - j - k) * fact k)).
    2 : { rewrite H7 at 2. rewrite Nat.div_mul. rewrite H4. rewrite Nat.div_mul. rewrite H7.
          replace (s * (fact j * fact (n - j))) with ((s * fact (n-j)) * (fact (j))) by lia.
          replace (fact j * fact (n - j - k) * fact k) with (fact (n - j - k) * fact k * fact j) by lia.
          rewrite Nat.Div0.div_mul_cancel_r. rewrite Nat.mul_comm with (m := fact k). 
          rewrite H4. replace (s * (p * (fact k * fact (n - j - k)))) with (s * p * (fact k * fact (n - j - k))) by lia.
          rewrite Nat.div_mul. lia. apply Nat.neq_mul_0. split; apply fact_neq_0. apply fact_neq_0. apply Nat.neq_mul_0; split; apply fact_neq_0.
          apply Nat.neq_mul_0; split; apply fact_neq_0.
    }
    replace (fact n / (fact k * fact (n - k)) * (fact (n - k) / (fact j * fact (n - k - j)))) with
            (fact n / (fact j * fact (n - j - k) * fact k)).
    2 : { rewrite H6 at 2. rewrite Nat.div_mul. rewrite H5. rewrite Nat.div_mul. rewrite H6.
          replace (r * (fact k * fact (n - k))) with ((r * fact (n-k)) * (fact (k))) by lia.
          replace (fact j * fact (n - j - k) * fact k) with (fact (n - j - k) * fact j * fact k) by lia.
          rewrite Nat.Div0.div_mul_cancel_r. rewrite Nat.mul_comm with (m := fact j). 
          replace (n - j - k) with (n - k - j) by lia. rewrite H5.
          replace (r * (q * (fact j * fact (n - k - j)))) with (r * q * (fact j * fact (n - k - j))) by lia.
          rewrite Nat.div_mul. lia. apply Nat.neq_mul_0; split; apply fact_neq_0. apply fact_neq_0. apply Nat.neq_mul_0; split; apply fact_neq_0.
          apply Nat.neq_mul_0; split; apply fact_neq_0.
     }
     lia.
Qed.

Open Scope R_scope.

Lemma lemma_16_4 : forall n,
  sum_f 0 n (fun k => INR (n ∁ k)) = 2^n.
Proof.
  intros n. pose proof (Binomial_Theorem 1 1 n) as H1. replace (1 + 1) with 2 in H1 by lra.
  rewrite H1. apply sum_f_equiv; try lia. intros k H2. repeat rewrite pow1. lra.
Qed.

Lemma lemma_16_5 : forall n,
  (n > 0)%nat -> sum_f 0 n (fun k => (-1)^k * INR (n ∁ k)) = 0.
Proof.
  intros n H1. pose proof (Binomial_Theorem 1 (-1) n) as H2. replace (1 + -1) with 0 in H2 by lra.
  rewrite pow_i in H2; try lia. rewrite H2. apply sum_f_equiv; try lia. intros k H4. repeat rewrite pow1. lra.
Qed.

Ltac simplify_nat_choose :=
  repeat match goal with
         | [ |- context[(?n ∁ ?k)] ] =>
           let C := eval compute in (choose n k) in
           change (n ∁ k) with C
         end.

Ltac simplify_power_expr :=
  repeat match goal with
  | |- context[?base ^ (?n - ?m)] =>
    let result := eval compute in (n - m)%nat in
    replace ((n - m)%nat) with (result) by (
      simpl; lia
    )
  end.

Ltac simplify_binomial_expansion :=
  rewrite Binomial_Theorem; repeat rewrite sum_f_i_Sn_f; try lia; rewrite sum_f_0_0; simplify_nat_choose; unfold INR; simplify_power_expr; field_simplify.

(* dont forget that our x is 2x and y is 3y*)
Compute ((8 ∁ 3) * 2^5 * 3^3)%nat.

Lemma lemma_16_6 : forall x y, (2 * x + 3 * y)^8 = 256 * x ^ 8 + 3072 * x ^ 7 * y + 16128 * x ^ 6 * y ^ 2 + 48384 * x ^ 5 * y ^ 3 + 90720 * x ^ 4 * y ^ 4 + 108864 * x ^ 3 * y ^ 5 + 81648 * x ^ 2 * y ^ 6 + 34992 * x * y ^ 7 + 6561 * y ^ 8.
Proof.
  intros x y. simplify_binomial_expansion. reflexivity.
Qed.

Open Scope nat_scope.

Lemma mul_div_cancel_l  : forall a b c,
  c <> 0 -> Nat.divide c b -> a * (b / c) = (a * b) / c.
Proof.
  intros a b c H1 [k H2]. rewrite H2. rewrite Nat.div_mul; auto. rewrite Nat.Lcm0.divide_div_mul_exact. 2 : { exists k. lia. }
  rewrite Nat.div_mul; lia.
Qed.

Close Scope nat_scope.

Section section_16_7.
  Local Definition choose := Binomial_R.choose.

  Lemma lemma_16_7 : forall n k,
    (n >= k)%nat -> (k > 0)%nat -> INR k * choose n k = INR n * choose (n - 1) (k - 1).
  Proof.
    intros n k H1 H2. repeat rewrite n_choose_k_def; try lia. replace (n - 1 - (k - 1)) with (n - k) by lia.
    apply Nat.mul_cancel_r with (p := fact (n - k)); (try apply fact_neq_0).
    replace (k * (fact n / (fact k * fact (n - k))) * fact (n - k)) with (k * fact n / fact k).
    2 : { replace (k * (fact n / (fact k * fact (n - k))) * fact (n - k)) with (k * fact n * fact (n - k) / (fact k * fact (n - k))).
          rewrite Nat.Div0.div_mul_cancel_r; try lia. apply fact_neq_0. replace (k * (fact n / (fact k * fact (n - k))) * fact (n - k))
          with (k * (fact (n -k) * (fact (n) / (fact k * fact (n - k))))) by lia. rewrite mul_div_cancel_l.
          2 : { apply Nat.neq_mul_0; split; apply fact_neq_0. } 2 : { apply fact_div; lia. } replace (fact k * fact (n - k)) with (fact (n - k) * fact k) by lia.
          rewrite Nat.Div0.div_mul_cancel_l. 2 : { apply fact_neq_0. } rewrite <- Nat.mul_assoc. replace (fact n * fact (n - k)) with (fact (n - k) * fact n) by lia.
          rewrite Nat.Lcm0.divide_div_mul_exact. 2 : { unfold Nat.divide. pose proof (fact_div n k ltac : (lia)) as [p H3]. exists (p * fact (n - k)). lia. }
          rewrite Nat.Div0.div_mul_cancel_l. 2 : { apply fact_neq_0. } lia.
    }
    replace (n * (fact (n - 1) / (fact (k - 1) * fact (n - k))) * fact (n - k)) with ((n * fact (n - 1)) / fact (k - 1)) by admit.
    replace n with (S (n - 1)) at 2 by lia. rewrite <- fact_simpl. replace (S (n - 1)) with n by lia.
    replace (n - 1) with 
  Qed.
End section_16_7.

