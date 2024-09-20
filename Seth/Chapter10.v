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


Section section_10_2.
  Open Scope set_scope.

  Definition A : Ensemble (Z * Z) := fun  p =>
    let (x, y) := p in (4 | x - y).

  Definition B : Ensemble (Z * Z) := fun p =>
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
  Open Scope set_scope.

  Definition X : Ensemble Z := fun x => x ≡ -1 (mod 6).

  Definition Y : Ensemble Z := fun y => y ≡ 2 (mod 3).

  Lemma lemma_10_3 : X ⊆ Y.
  Proof.
    unfold Included. intros x H1. unfold In, X, Y in *.
    destruct H1 as [k H2]. exists (2 * k - 1). lia.
  Qed.
  
End section_10_3.

Open Scope set_scope.

Lemma lemma_10_4_a : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ ⊆ (A′ ⋃ B′).
Proof.
  intros U A B. intros x H1. unfold In. assert (x ∉ A \/ x ∈ A) as [H2 | H2] by tauto;
  assert (x ∉ B \/ x ∈ B) as [H3 | H3] by tauto; try (solve [apply Union_introl; auto] || solve [apply Union_intror; auto]).
  pose proof (Intersection_intro U A B x H2 H3) as H4. exfalso. apply H1. auto.
Qed.