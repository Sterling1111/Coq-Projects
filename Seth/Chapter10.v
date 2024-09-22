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

Lemma In_Union_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋃ B) <-> x ∈ A \/ x ∈ B.
Proof.
  intros; split; [apply Union_inv | intros [H1 | H1]; [apply Union_introl; auto | apply Union_intror; auto]].
Qed.

Lemma In_Intersection_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋂ B) <-> x ∈ A /\ x ∈ B.
Proof.
  intros; split; [apply Intersection_inv | intros [H1 H2]; apply Intersection_intro; auto].
Qed.

Lemma Complement_def : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A′ <-> x ∉ A.
Proof.
  intros U A x; split; auto.
Qed.

Lemma In_Setminus_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A − B) <-> x ∈ A /\ x ∉ B.
Proof.
  intros U A B x; split.
  - intros H1. auto.
  - intros [H1 H2]. unfold Setminus. unfold In. auto.
Qed.

Lemma Setminus_def : forall (U : Type) (A B : Ensemble U),
  (A − B) = A ⋂ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - apply In_Intersection_def. apply In_Setminus_def in H1. auto.
  - apply In_Intersection_def in H1. apply In_Setminus_def. auto.
Qed.

Ltac break_union_intersection :=
  repeat match goal with
  | [ H: ?x ∈ _ ⋃ _ |- _] => apply In_Union_def in H
  | [ H: ?x ∈ _ ⋂ _ |- _ ] => apply In_Intersection_def in H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: _ \/ _ |- _ ] => destruct H
  end.

Ltac solve_in_Union :=
  simpl; auto;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋃ _ ] => apply In_Union_def; solve [ left; solve_in_Union | right; solve_in_Union ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac solve_in_Intersection :=
  simpl; auto;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac solve_in_Intersection_Union_helper :=
  intros; break_union_intersection; simpl; auto; (try contradiction);
  solve
  [match goal with | [ |- ?G ] => idtac G end | 

  match goal with
  | [ |- ?x ∈ ?A \/ ?x ∈ ?A′ ] => apply classic
  | [ |- ?x ∈ Full_set _ ] => apply Full_intro
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection_Union_helper
  | [ |- ?x ∈ _ ⋃ _ ] => apply In_Union_def; (try tauto);  solve [ left; solve_in_Intersection_Union_helper | right; solve_in_Intersection_Union_helper ]
  | [ |- ?G ] => fail "Goal not solvable"
  end].

Ltac solve_in_Intersection_Union := break_union_intersection; solve_in_Intersection_Union_helper.

Ltac solve_set_equality := intros; apply set_equal_def; intros x; split; intros; solve_in_Intersection_Union.

Lemma Union_comm : forall (U : Type) (A B : Ensemble U),
  A ⋃ B = B ⋃ A.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_comm : forall (U : Type) (A B : Ensemble U),
  A ⋂ B = B ⋂ A.
Proof.
  solve_set_equality.
Qed.

Lemma Union_assoc : forall (U : Type) (A B C : Ensemble U),
  A ⋃ (B ⋃ C) = (A ⋃ B) ⋃ C.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_assoc : forall (U : Type) (A B C : Ensemble U),
  A ⋂ (B ⋂ C) = (A ⋂ B) ⋂ C.
Proof.
  solve_set_equality.
Qed.


Lemma Union_Distrib_Intersection : forall (U : Type) (A B C : Ensemble U),
  A ⋃ (B ⋂ C) = (A ⋃ B) ⋂ (A ⋃ C).
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_Distrib_Union : forall (U : Type) (A B C : Ensemble U),
  A ⋂ (B ⋃ C) = (A ⋂ B) ⋃ (A ⋂ C).
Proof.
  solve_set_equality.
Qed.

Lemma Union_Identity : forall (U : Type) (A : Ensemble U),
  ∅ ⋃ A = A.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_Identity : forall (U : Type) (A : Ensemble U),
  A ⋂ Full_set U = A.
Proof.
  solve_set_equality.
Qed.

Lemma Union_Complement : forall (U : Type) (A : Ensemble U),
  A′ ⋃ A = Full_set U.
Proof.
  intros U A. apply set_equal_def. intros x. split; intros; break_union_intersection.
  - apply Full_intro.
  - apply Full_intro.
  - apply In_Union_def. tauto.
Qed.

Lemma Intersection_Complement : forall (U : Type) (A : Ensemble U),
  A ⋂ A′ = ∅.
Proof.
  solve_set_equality.
Qed.

Lemma De_Morgan_Union : forall (U : Type) (A B : Ensemble U),
  (A ⋃ B)′ = A′ ⋂ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - apply In_Intersection_def. apply not_or_and. intros H2. apply H1. apply In_Union_def. auto.
  - apply In_Intersection_def in H1 as [H1 H2]. intros H3. apply In_Union_def in H3 as [H3 | H3]; auto.
Qed.

Lemma De_Morgan_Intersection : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ = A′ ⋃ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - apply In_Union_def. apply not_and_or. intros H2. apply H1. apply In_Intersection_def. auto.
  - apply In_Union_def in H1. apply or_not_and in H1. intros H2. apply H1. apply In_Intersection_def. auto.
Qed.

Lemma not_in_Union : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A /\ x ∉ B <-> x ∉ A ⋃ B.
Proof.
  intros U A B x. split.
  - intros [H1 H2]. intros H3. apply In_Union_def in H3. tauto.
  - intros H1. split; intros H2; apply H1; apply In_Union_def; auto.
Qed.

Lemma not_in_Intersection : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A \/ x ∉ B <-> x ∉ A ⋂ B.
Proof.
  intros U A B x. split.
  - intros [H1 | H1]; intros H2; apply In_Intersection_def in H2; tauto.
  - intros H1. destruct (In_or_not U A x) as [H2 | H2]; destruct (In_or_not U B x) as [H3 | H3]; auto.
    exfalso. apply H1. apply In_Intersection_def; auto.
Qed.

Lemma not_in_Complement : forall (U : Type) (A : Ensemble U) (x : U),
  x ∉ A <-> x ∈ A′.
Proof.
  intros U A x. split; auto.
Qed.

Lemma not_in_Setminus : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A − B <-> x ∉ A \/ x ∈ B.
Proof.
  intros U A B x. split.
  - intros H1. destruct (In_or_not U B x) as [H2 | H2]; auto. left. intros H3. apply H1. apply In_Setminus_def. auto.
  - intros [H1 | H1] H2.
    -- apply H1. apply In_Setminus_def in H2 as [H2 H3]. auto.
    -- apply In_Setminus_def in H2 as [H2 H3]. auto.
Qed.

Lemma Complement_Complement : forall (U : Type) (A : Ensemble U),
  A′′ = A.
Proof.
  intros U A. apply set_equal_def. intros x. split; intros H1.
  - pose proof In_or_not U A x as [H2 | H2]; auto. exfalso. apply H1. apply H2.
  - intros H2. apply H2. auto.
Qed.

Lemma Setminus_Complement : forall (U : Type) (A B : Ensemble U),
  (A − B)′ = A′ ⋃ B.
Proof.
  intros U A B. rewrite Setminus_def. rewrite De_Morgan_Intersection. rewrite Complement_Complement. reflexivity.
Qed.

  
Ltac break_union_intersection_2 :=
  repeat match goal with
  | [ H: ?x ∈ _ ⋃ _ |- _ ] => apply In_Union_def in H
  | [ H: ?x ∈ _ ⋂ _ |- _ ] => apply In_Intersection_def in H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: _ \/ _ |- _ ] => destruct H
  | [ H: ?x ∈ (?A ⋃ ?B)′ |- _ ] => rewrite De_Morgan_Union in H
  | [ H: ?x ∈ (?A ⋂ ?B)′ |- _ ] => rewrite De_Morgan_Intersection in H
  | [ H: ?x ∈ (?A − ?B)′ |- _ ] => rewrite Setminus_Complement in H
  | [ H: ?x ∈ _ − _ |- _ ] => rewrite In_Setminus_def in H
  | [ H: ?x ∉ _ ⋃ _ |- _ ] => rewrite not_in_Union in H
  | [ H: ?x ∉ _ ⋂ _ |- _ ] => rewrite not_in_Intersection in H
  | [ H: ?x ∉ _ |- _ ] => rewrite not_in_Complement in H
  | [ H: ?x ∉ _ − _ |- _ ] => rewrite not_in_Setminus in H
  end.

Ltac solve_in_Intersection_Union_helper_2 :=
  intros; break_union_intersection_2; simpl; auto; (try contradiction);
  solve
  [ match goal with
    | [ |- ?G ] => idtac G
    end | 
    match goal with
    | [ |- ?x ∉ _ ⋃ _ ] => apply not_in_Union; split; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∉ _ ⋂ _ ] => apply not_in_Intersection; (try tauto); solve [ left; solve_in_Intersection_Union_helper_2 | right; solve_in_Intersection_Union_helper_2 ]
    | [ |- ?x ∉ _ − _ ] => rewrite not_in_Setminus; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∉ _ ] => rewrite not_in_Complement; solve_in_Intersection_Union_helper_2 
    | [ |- ?x ∈ Full_set _ ] => apply Full_intro
    | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
    | [ |- ?x ∈ _ − _] => try (apply In_Setminus_def); split; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ (_ ⋂ _)′ ] => rewrite De_Morgan_Intersection; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ (_ ⋃ _)′ ] => rewrite De_Morgan_Union; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ (_ − _)′ ] => rewrite Setminus_Complement; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ (_)′′ ] => rewrite Complement_Complement; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection_Union_helper_2
    | [ |- ?x ∈ _ ⋃ _ ] => apply In_Union_def; (try tauto); solve [ left; solve_in_Intersection_Union_helper_2 | right; solve_in_Intersection_Union_helper_2 ]
    | [ |- ?G ] => fail "Goal not solvable"
    end ].

Ltac in_list x l :=
  match l with
  | context[x] => constr:(true)
  | _ => constr:(false)
  end.


Ltac find_sets_in_expr E acc :=
  match E with
  | ?A ⋃ ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A ⋂ ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A − ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A′ => find_sets_in_expr A acc
  | ?A =>
      let is_in := in_list A acc in
      match is_in with
      | true => acc (* Do nothing, A is already in the list *)
      | false => constr:(A :: acc) (* Add A to the accumulator *)
      end
  end.


Ltac find_sets_in_goal U :=
  match goal with
  | |- ?x ∈ ?LHS <-> ?x ∈ ?RHS =>
      let acc := constr:(@nil (Ensemble U)) in
      let L := find_sets_in_expr LHS acc in
      find_sets_in_expr RHS L
  end.

Ltac pose_in_or_not_for_sets U x :=
  let sets := find_sets_in_goal U in
  let rec process_sets s :=
    match s with
    | nil => idtac "All sets found:"; idtac sets
    | cons ?A ?xs =>
        pose proof (In_or_not U A x);
        process_sets xs
    end
  in
  process_sets sets.

Ltac solve_set_equality_auto :=
  intros U; intros; apply set_equal_def; intros x; pose_in_or_not_for_sets U x; split; solve_in_Intersection_Union_helper_2.

Lemma De_Morgan_Intersection_2 : forall (U : Type) (A B : Ensemble U),
  A = A.
Proof.
  solve_set_equality_auto.
Qed.

Lemma testinggg : forall (U : Type) (A B : Ensemble U),
  (A − B)′ = A′ ⋃ B.
Proof.
  solve_set_equality_auto.
Qed.

Lemma set_mins_tester : forall (U : Type) (A B C : Ensemble U),
   (A − (B ⋃ C)) = (A ⋂ (B′ ⋂ C′)).
Proof.
  solve_set_equality_auto.
Qed.

Lemma set_difference_union : forall (U : Type) (A B C : Ensemble U),
  (A − B) ⋃ (B − C) = (A ⋃ B) − (B ⋂ C).
Proof.
  solve_set_equality_auto.
Qed.

Lemma complex_set_lemma :
  forall (U : Type) (A B C : Ensemble U),
    ((A ⋂ (B ⋃ C)) ⋂ (A − B)) ⋂ (B ⋂ C′) = ∅.
Proof.
  solve_set_equality_auto.
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
Proof. solve_in_Union. Qed.

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

Lemma frac_not_Z : forall (x : Z) (a b : R), (exists z1, IZR z1 < a / b < IZR (z1 + 1)) -> a / b <> IZR x.
Proof.
  intros x a b [z1 H1] H2. pose proof (classic (a = 0)) as [H3 | H3]; pose proof (classic (b = 0)) as [H4 | H4];
   try (replace (a / b) with 0 in H1 by (subst; unfold Rdiv; try rewrite Rinv_0; lra); assert (z1 < 0 < z1 + 1)%Z as H5 by (split; first [apply lt_IZR | apply IZR_lt]; lra); lia).
   rewrite H2 in H1. destruct H1 as [H1 H5]. apply lt_IZR in H1. apply lt_IZR in H5. lia.
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
    assert (2 / 3 <> IZR y) as H3. { apply frac_not_Z. exists 0%Z. simpl. lra. } auto.
  Qed.
  
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
  intros U A B x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_4_b : forall (U : Type) (A B : Ensemble U),
  (A′ ⋃ B′) ⊆ (A ⋂ B)′.
Proof.
  intros U A B. intros x H1 H2. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_4_c : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ = (A′ ⋃ B′).
Proof.
  solve_set_equality_auto.
Qed.

Lemma lemma_10_5 : forall (U : Type) (X Y : Ensemble U),
  (X − (X − Y)) ⊆ X ⋂ Y.
Proof.
  intros U X Y x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_6 : forall (U : Type) (X : Ensemble U),
  X ⋃ ∅ = X.
Proof.
  solve_set_equality_auto.
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

Lemma lemma_10_8_a : forall (U : Type) (A B C : Ensemble U),
  A − (B ⋂ C) ⊆ (A − B) ⋃ (A − C).
Proof.
  intros U A B C x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_8_b : forall (U : Type) (A B C : Ensemble U),
  (A − B) ⋃ (A − C) ⊆ A − (B ⋂ C).
Proof.
  intros U A B C x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_8_c : forall (U : Type) (A B C : Ensemble U),
  A − (B ⋂ C) = (A − B) ⋃ (A − C).
Proof.
  intros U A B C. apply subset_subset_eq_iff. split; [apply lemma_10_8_a | apply lemma_10_8_b].
Qed.