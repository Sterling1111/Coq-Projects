Require Import ZArith Lia Classical.
From Seth Require Export Chapter6.

Open Scope Z_scope.

Lemma contra_2 : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q H1 H2 H3. apply H2. apply H1. apply H3.
Qed.

Lemma contra_2' : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof. intros; tauto. Qed.

Lemma contra_2_reverse : forall P Q : Prop, (~Q -> ~P) -> (P -> Q).
Proof. intros P Q H1 H2. pose proof classic Q as [H3 | H3]; auto. exfalso. apply H1. apply H3. apply H2.
Qed.

Lemma contra_2_reverse' : forall P Q : Prop, (~Q -> ~P) -> (P -> Q).
Proof. intros; tauto. Qed.

Lemma not_odd_iff_even_Z : forall z : Z, ~Z.Odd z <-> Z.Even z.
Proof.
    intros z. split.
    - intros H1. pose proof Z.Even_or_Odd z as [H2 | H2]; tauto.
    - intros H1 H2. pose proof Z.Even_Odd_False z as H3. tauto.
Qed.

Lemma NNPP_inverse : forall P : Prop, P -> ~~P.
Proof. intros P H1 H2. apply H2. apply H1. Qed. 

Lemma not_even_iff_odd_Z : forall z : Z, ~Z.Even z <-> Z.Odd z.
Proof.
    intros z. split.
    - rewrite <- not_odd_iff_even_Z. apply NNPP.
    - rewrite <- not_odd_iff_even_Z. apply NNPP_inverse.
Qed.

Lemma lemma_7_1 : forall a : Z, Z.Odd (a^2 + 3) -> Z.Even a.
Proof.
    intros a. apply contra_2_reverse. intros H1. rewrite not_even_iff_odd_Z in H1.
    rewrite not_odd_iff_even_Z. destruct H1 as [k H1]. exists (2 * k^2 + 2 * k + 2). lia.
Qed.

Lemma lemma_7_2 : forall x y : Z, Z.Even (x * y + y^2) -> (Z.Odd x \/ Z.Even y).
Proof.
    intros x y. apply contra_2_reverse. intros H1. apply not_or_and in H1 as [H1 H2]. 
    rewrite not_even_iff_odd_Z in H2. rewrite not_odd_iff_even_Z in H1.
    rewrite not_even_iff_odd_Z. apply even_plus_odd_Z.
    - apply even_mult_Z_l; auto.
    - apply lemma_6_3; auto.
Qed.

Lemma lemma_7_3 : forall s : Z, Z.Odd s <-> Z.Odd (s^3).
Proof.
    intros s. split.
    - intros H1. replace (s^3) with (s * s * s) by lia. repeat apply odd_mult_odd_Z; auto.
    - apply contra_2_reverse. intros H1. rewrite not_odd_iff_even_Z in H1. rewrite not_odd_iff_even_Z.
      destruct H1 as [k H1]. exists (4 * k^3). lia.
Qed.

(* the students mistake is that the contrapositive would mean assuming that x is not even *)
Lemma lemma_7_4 : forall x : Z, (2 | x) -> Z.Even x.
Proof.
    intro x. apply contra_2_reverse. intros H1 [k H2]. apply not_even_iff_odd_Z in H1 as [j H1]. lia.
Qed.

Lemma lemma_7_5 : forall a b c d : Z, (a | c) -> (b | d) -> (a * b | c * d).
Proof.
    intros a b c d [k H1] [l H2]. rewrite H1, H2. exists (k * l). lia.
Qed.

Lemma lemma_7_6 : forall a b c d : Z,
    (((a | c) /\ (b | d)) -> (a + b | c + d)) -> (~(a + b | c + d) -> (~(a | c) \/ ~(b | d))).
Proof.
    intros a b c d H1. apply contra_2_reverse. intro H2. apply NNPP_inverse. apply H1.
    apply not_or_and in H2 as [H2 H3]. apply NNPP in H2, H3. auto.
Qed.

Lemma lemma_7_7 : forall a, ~(4 | a^2) -> Z.Odd a.
Proof.
    intros a. apply contra_2_reverse. intros H1. apply not_odd_iff_even_Z in H1 as [k H1]. apply NNPP_inverse.
    exists (k^2). lia.
Qed.

Lemma lemma_7_8 : forall x : Z, Z.Even (5 * x - 1) -> Z.Odd x.
Proof.
    intros x. apply contra_2_reverse. intros H2. apply not_odd_iff_even_Z in H2 as [k H2].
    apply not_even_iff_odd_Z. rewrite H2. exists (5 * k - 1). lia.
Qed.

Lemma lemma_7_8' : forall x : Z, Z.Even (5 * x - 1) -> Z.Odd x.
Proof.
    intros x [j H1]. pose proof (Z.Even_or_Odd x) as [[k H2] | H2]; auto.
    rewrite H2 in H1. assert (H3 : 2 * (5 * k) = 2 * j + 1) by lia. (* lia. would finish it now *)
    assert (H4 : Z.Even (2 * (5 * k))) by (exists (5 * k); lia).
    assert (H5 : Z.Odd (2 * j + 1)) by (exists k; lia). pose proof (Z.Even_Odd_False (2 * j + 1)) as H6.
    exfalso. apply H6.
    - rewrite <- H3. apply H4.
    - apply H5.
     (* we have even = odd impossible by QRT*) 
Qed.