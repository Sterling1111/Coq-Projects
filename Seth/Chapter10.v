Require Import ZArith Lia Classical Reals Lra Classical_sets List Ensembles.
Import ListNotations.
From Seth Require Export Chapter9.

Declare Scope set_scope.
Delimit Scope set_scope with set.

(* Define notations within the custom scope with improved precedence *)
Notation "x ∈ A" := (In _ A x) (at level 40) : set_scope.
Notation "x ∉ A" := (~ In _ A x) (at level 40) : set_scope.
Notation "A ⊆ B" := (Included _ A B) (at level 40) : set_scope.
Notation "A ⊈ B" := (~ Included _ A B) (at level 40) : set_scope.
Notation "A ⊊ B" := (Strict_Included _ A B) (at level 40) : set_scope.
Notation "A ⋃ B" := (Union _ A B) (at level 30) : set_scope.
Notation "A ⋂ B" := (Intersection _ A B) (at level 30) : set_scope.
Notation "A − B" := (Setminus _ A B) (at level 30) : set_scope.
Notation "A ′" := (Complement _ A) (at level 20, format "A ′") : set_scope.
Notation "∅" := (Empty_set _) : set_scope.

Open Scope set_scope.

Fixpoint list_to_ensemble {U : Type} (l : list U) : Ensemble U :=
  match l with
  | nil => Empty_set U
  | cons x xs => Union U (Singleton U x) (list_to_ensemble xs)
  end.

Notation "{ x1 , .. , xn }" :=
  (@list_to_ensemble _ (cons x1 .. (cons xn nil) ..)).

Lemma Union_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋃ B) <-> x ∈ A \/ x ∈ B.
Proof.
  intros; split; [apply Union_inv | intros [H1 | H1]; [apply Union_introl; auto | apply Union_intror; auto]].
Qed.

Lemma Intersection_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋂ B) <-> x ∈ A /\ x ∈ B.
Proof.
  intros; split; [apply Intersection_inv | intros [H1 H2]; apply Intersection_intro; auto].
Qed.

Lemma Complement_def : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A′ <-> x ∉ A.
Proof.
  intros U A x; split; auto.
Qed.

Lemma Setminus_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A − B) <-> x ∈ A /\ x ∉ B.
Proof.
  intros U A B x; split.
  - intros H1. auto.
  - intros [H1 H2]. unfold Setminus. unfold In. auto.
Qed.

Lemma In_or_not : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A \/ x ∉ A.
Proof.
  intros U A x. apply classic.
Qed.

Lemma set_equal_def : forall (U : Type) (A B : Ensemble U),
  A = B <-> (forall x : U, x ∈ A <-> x ∈ B).
Proof.
  intros U A B; split; intros H1.
  - intros x; rewrite H1; reflexivity.
  - apply Extensionality_Ensembles; split; intros x H2; apply H1; auto.
Qed.

Lemma subset_subset_eq_iff : forall (U : Type) (A B : Ensemble U),
  A ⊆ B /\ B ⊆ A <-> A = B.
Proof.
  intros U A B; split.
  - intros [H1 H2]. apply Extensionality_Ensembles; split; auto.
  - intros H1. rewrite H1. unfold Included. auto.
Qed.

Ltac solve_in_ensemble :=
  simpl;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋃ _ ] => apply Union_def; [ right; solve_in_ensemble || left; solve_in_ensemble ]
  | _ => fail "Goal not solvable"
  end.

Lemma not_in_Union : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A /\ x ∉ B -> x ∉ A ⋃ B.
Proof.
  intros U A B x [H1 H2]. intros H3. apply Union_def in H3 as [H3 | H3]; auto.
Qed.

Ltac solve_not_in_ensemble :=
  simpl;
  match goal with
  | [ |- ?x ∉ ∅ ] => intros H_69420; inversion H_69420
  | [ |- ?x ∉ Singleton _ _ ] => intros H_69420; apply Singleton_inv in H_69420; (try inversion H_69420; try nia; try nra)
  | [ |- ?x ∉ _ ⋃ _ ] => apply not_in_Union; split; solve_not_in_ensemble
  | [ |- ?G ] => idtac G; fail "Goal not solvable"
  end.

Lemma lemma_10_1_a : 3 ∈ {1, 2, 3, 4, 5, 6, 7}.
Proof. solve_in_ensemble. Qed.

Lemma asdlfasdf : 3 ∉ {1, 2, 4, 5, 6, 7}.
Proof.
  solve_not_in_ensemble.
Qed.

Open Scope R_scope.

Axiom PI_int_bound : 3 < PI < 4.

Lemma lemma_10_1_b : PI ∉ {1, 2, 3, 4, 5, 6, 7}.
Proof.
  pose proof PI_int_bound as H1. solve_not_in_ensemble.
Qed.

Lemma lemma_10_1_c : PI ∈ Full_set R.
Proof.
  apply Full_intro.
Qed.

Lemma frac_not_Z : forall (x : Z) (a b : R), (exists z1 z2, IZR z1 < a / b < IZR z2) -> a / b <> IZR x.
Proof.
  intros x a b [z1 [z2 H1]] H2.
  assert (x < 0 \/ x = 0 \/ x >= 1)%Z as [H3 | [H3 | H3]] by lia.
  - assert (IZR x < 0) as H4. { apply IZR_lt in H3; auto. } lra.
  - rewrite H2 in H1. lra.
  - assert (IZR x >= 1) as H3. { apply IZR_ge; auto. } lra.
Qed.


Section section_10_1_d_e.
  Let A : Ensemble R := fun x => x < 1.
  Let B : Ensemble R := fun x => x < 1 /\ exists y, x = IZR y.

  Lemma lemma_10_1_d : 2/3 ∈ A.
  Proof.
    unfold In, A. lra.
  Qed.

  Lemma lemma_10_1_e : 2/3 ∉ B.
  Proof.
    unfold In, B. intros [H1 H2]. destruct H2 as [y H2]. 
    assert (2/3 <)

  
End section_10_1_d_e.


Close Scope R_scope.

Section section_10_2.
  Let A : Ensemble (Z * Z) := fun  p =>
    let (x, y) := p in (4 | x - y).

  Let B : Ensemble (Z * Z) := fun p =>
    let (x, y) := p in (Z.Even x <-> Z.Even y).

  Lemma lemma_10_2 : A ⊆ B.
  Proof.
    unfold Included. intros (x, y) [i H1]. unfold In, A, B in *. split.
    - intros H2. destruct (Z.Even_or_Odd y) as [H3 | H3]; auto.
      assert (H4 : Z.Even (x - y)). { exists (2*i). lia. }
      assert (H5 : Z.Odd (x - y)). { apply odd_plus_Z. left; split; (try  rewrite <- odd_sign_Z); auto. }
      exfalso. apply Z.Even_Odd_False with (x := x - y); auto.
    - intros H2. assert (Z.Even (x - y)) as H3. { exists (2*i); lia. }
      apply even_plus_Z in H3 as [[H3 _] | [_ H3]]; auto. rewrite <- odd_sign_Z in H3. exfalso.
      apply Z.Even_Odd_False with (x := y); auto.
  Qed.
End section_10_2.

Section section_10_3.
  Let X : Ensemble Z := fun x => x ≡ -1 (mod 6).

  Let Y : Ensemble Z := fun y => y ≡ 2 (mod 3).

  Lemma lemma_10_3 : X ⊆ Y.
  Proof.
    unfold Included. intros x H1. unfold In, X, Y in *.
    destruct H1 as [k H2]. exists (2 * k - 1). lia.
  Qed.
  
End section_10_3.

Lemma lemma_10_4_a : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ ⊆ (A′ ⋃ B′).
Proof.
  intros U A B. intros x H1. assert (x ∈ A \/ x ∉ A) as [H2 | H2] by (apply In_or_not);
  assert (x ∈ B \/ x ∉ B) as [H3 | H3] by (apply In_or_not); try (solve [apply Union_introl; auto] || solve [apply Union_intror; auto]).
  pose proof (Intersection_intro U A B x H2 H3) as H4. exfalso. apply H1. auto.
Qed.

Lemma lemma_10_4_b : forall (U : Type) (A B : Ensemble U),
  (A′ ⋃ B′) ⊆ (A ⋂ B)′.
Proof.
  intros U A B. intros x H1 H2. assert (x ∈ A \/ x ∉ A) as [H3 | H3] by (apply In_or_not);
  assert (x ∈ B \/ x ∉ B) as [H4 | H4] by (apply In_or_not); apply Intersection_def in H2 as [H5 H6];
  apply Union_def in H1 as [H1 | H1]; auto.
Qed.

Lemma lemma_10_4_c : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ = (A′ ⋃ B′).
Proof.
  intros U A B. apply subset_subset_eq_iff; split; [apply lemma_10_4_a | apply lemma_10_4_b].
Qed.

Lemma lemma_10_5 : forall (U : Type) (X Y : Ensemble U),
  (X − (X − Y)) ⊆ X ⋂ Y.
Proof.
  intros U X Y x H1. apply Setminus_def in H1 as [H2 H3].
  apply Intersection_def; split; auto. pose proof (In_or_not U Y x) as [H4 | H4]; auto.
  exfalso. apply H3. apply Setminus_def; auto.
Qed.

Lemma lemma_10_6 : forall (U : Type) (X : Ensemble U),
  X ⋃ ∅ = X.
Proof.
  intros U X. apply set_equal_def. intros x. split.
  - intros H1. apply Union_def in H1 as [H1 | H1]; auto. contradiction.
  - intros H1. apply Union_def. auto.
Qed.

Section section_10_7.
  Variable n : Z.
  Let A : Ensemble Z := fun x => (n | x).
  Let B : Ensemble Z := fun x => x ≡ 0 (mod n).

  Lemma lemma_10_7 : A = B.
  Proof.
    apply set_equal_def. intros x. split.
    - intros H1. unfold In, A, B in *. destruct H1 as [k H1]. exists k. lia.
    - intros H1. unfold In, A, B in *. destruct H1 as [k H1]. exists k. lia.
  Qed.
End section_10_7.

