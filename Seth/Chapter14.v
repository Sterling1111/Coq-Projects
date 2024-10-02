Require Import ZArith Lia Classical Reals Lra Classical_sets List
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image.
From Seth Require Export Chapter13.
Import ListNotations SetNotations.

Lemma In_Power_set_def : forall (U : Type) (A B : Ensemble U),
  B ∈ ℙ(A) <-> B ⊆ A.
Proof.
  intros U A B. split; intros H1.
  - unfold In, Power_set in H1. auto.
  - unfold In, Power_set. auto.
Qed.

Lemma Power_Set_equiv_Power_set : forall {U : Type} (A B : Ensemble U),
  B ∈ ℙ(A) <->  B ∈ (Powerset.Power_set U A).
Proof.
  intros U A B. split; intros H1.
  - rewrite In_Power_set_def in H1. constructor. auto.
  - rewrite In_Power_set_def. destruct H1 as [X H1]. auto.
Qed.

Lemma Finite_set_equiv_Finite : forall (U : Type) (A : Ensemble U),
  Finite_set A <-> Finite_sets.Finite U A.
Proof.
  intros U A. split.
  - intros [l H1]. generalize dependent A. induction l as [| h t IH].
    -- intros A H1. rewrite list_to_ensemble_nil in H1. rewrite <- H1. apply Empty_is_finite.
    -- intros A H1. rewrite list_to_ensemble_cons in H1. rewrite <- H1. destruct (classic (h ∈ list_to_ensemble t)) as [H2 | H2].
      + assert (⦃h⦄ ⋃ list_to_ensemble t = list_to_ensemble t) as H3.
        {
           apply set_equal_def. intros x. split; intros H3; try autoset.
           apply In_Union_def in H3 as [H3 | H3]; auto. apply In_singleton_def in H3. rewrite H3. apply H2.
        }
        rewrite H3 in H1. rewrite H3. specialize (IH A). rewrite <- H1 in IH at 2. specialize (IH H1). auto.
      + replace (⦃h⦄ ⋃ list_to_ensemble t) with (Add _ (list_to_ensemble t) h). 2 : { unfold Add; autoset. } 
        apply Union_is_finite; auto.
  - intros H1. induction H1 as [| A H1 IH].
    -- exists []. rewrite list_to_ensemble_nil. reflexivity.
    -- destruct IH as [l H2]. exists (x :: l). unfold Add. rewrite <- H2. autoset.
Qed.

Lemma Subset_Empty_def : forall (U : Type) (A : Ensemble U),
  A ⊆ ∅ <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - apply set_equal_def. intros x. split; intros H2.
    -- apply H1 in H2; auto.
    -- contradiction.
  - rewrite H1. apply Subset_refl.
Qed.

Lemma Empty_or_exists_In : forall (U : Type) (A : Ensemble U),
  A = ∅ \/ exists x : U, x ∈ A.
Proof.
  intros U A. destruct (classic (A = ∅)) as [H1 | H1]; auto; right.
  apply NNPP. intros H2. apply H1. apply set_equal_def. intros x; split; intro H3.
  - exfalso. apply H2. exists x. auto.
  - contradiction.
Qed.

Lemma In_singleton_def : forall (U : Type) (x y : U),
  x ∈ Singleton U y <-> x = y.
Proof.
  intros U x y. split; intros H1.
  - apply Singleton_inv in H1. auto.
  - apply Singleton_intro. auto.
Qed.

Lemma Power_set_Empty_1 : forall (U : Type),
  ℙ(∅ : Ensemble U) = Singleton (Ensemble U) (Empty_set _).
Proof.
  intros U. apply set_equal_def; intros x; split; intros H1. 
  - rewrite In_Power_set_def in H1. rewrite Subset_def in H1. pose proof (Empty_or_exists_In U x) as [H2 | [y H2]].
    -- rewrite H2. solve_in_Union.
    -- specialize (H1 y H2). contradiction.
  - rewrite In_Power_set_def. rewrite Subset_def. intros y H2. apply In_singleton_def in H1. rewrite H1 in H2. apply H2.
Qed.

Lemma Power_set_Empty_2 : forall (U : Type) (A : Ensemble U),
  ℙ(A) = ⦃⦃⦄⦄ <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - rewrite set_equal_def in H1. apply set_equal_def. intros x. split; intros H2.
    -- specialize (H1 A) as [H1 H3]. rewrite In_Power_set_def in H1. specialize (H1 (Subset_refl U A)). apply In_singleton_def in H1. autoset.
    -- contradiction.
  - rewrite H1. apply Power_set_Empty_1.
Qed.

Lemma Empty_In_Power_set : forall (U : Type) (A : Ensemble U),
  ∅ ∈ ℙ(A).
Proof.
  intros U A. rewrite In_Power_set_def. apply Empty_Subset.
Qed.

Section PowerSetBuilder.
  Fixpoint remove_duplicates_aux {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l acc : list U) : list U :=
    match l with
    | [] => rev acc
    | x :: xs =>
        if in_dec eq_dec x acc then
          remove_duplicates_aux eq_dec xs acc
        else
          remove_duplicates_aux eq_dec xs (x :: acc)
    end.

  Definition remove_duplicates {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l : list U) : list U :=
    remove_duplicates_aux eq_dec l [].

  Fixpoint PowerSetBuilder_aux {U : Type} (l : list U) : list (list U) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let ps := PowerSetBuilder_aux xs in
        ps ++ map (fun s => x :: s) ps
    end.

  Definition PowerSetBuilder {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l : list U) : Ensemble (Ensemble U) :=
    let l' := remove_duplicates eq_dec l in list_to_ensemble (map list_to_ensemble (PowerSetBuilder_aux l')).

Compute PowerSetBuilder Nat.eq_dec [1].

End PowerSetBuilder.

Lemma cardinal_Empty_1 : forall (U : Type) (A : Ensemble U),
  cardinal U (A) 0 <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - apply cardinal_invert in H1; auto.
  - rewrite H1. apply card_empty.
Qed.

Lemma cardinal_Empty_2 : forall (U : Type) (n : ℕ),
  |(∅ : Ensemble U)| = n -> n = 0.
Proof.
  intros U n H1. destruct n as [| n]; auto. exfalso. apply cardinal_invert in H1 as [A [x [H1 [H2 H3]]]].
  rewrite set_equal_def in H1. specialize (H1 x) as [H1 H4]. unfold Add in H4. assert (x ∈ A ⋃ ⦃x⦄) as H5.
  { apply In_Union_def. right. apply In_singleton_def. auto. } specialize (H4 H5). contradiction.
Qed.

Lemma cardinal_Singleton : forall (U : Type) (x : U),
  |⦃x⦄| = 1.
Proof.
  intros U x. replace (Singleton U x) with (∅ ⋃ Singleton U x) by autoset. apply card_add; [apply card_empty | autoset].
Qed.

Lemma cardinal_inifinite : forall (U : Type) (A : Ensemble U),
  ~Finite U A -> forall n : ℕ, ~ |A| = n.
Proof.
  intros U A H1 n H2. generalize dependent A. induction n as [| k IH].
  - intros A H1 H2. apply cardinal_invert in H2. apply H1. rewrite H2. apply Empty_is_finite.
  - intros A H1 H2. apply H1. apply cardinal_invert in H2 as [B [x [H2 [H3 H4]]]]. rewrite H2. apply Union_is_finite; auto.
    destruct k as [| k'].
    -- inversion H4. apply Empty_is_finite.
    -- exfalso. apply (IH B); auto. intros H5. apply H1. rewrite H2. apply Union_is_finite; auto.
Qed.

Lemma cardinal_minus : forall (U : Type) (A : Ensemble U) (h : U) (n : ℕ),
  |A| = S n -> h ∈ A -> |A − ⦃h⦄| = n.
Proof.
  intros U A h n H1 H2. replace (A − ⦃h⦄) with (Subtract U A h) by autoset.
  replace n with (Nat.pred (S n)) by lia.
  apply card_soustr_1; auto.
Qed.

Lemma In_Im_def : forall (U V : Type) (A : Ensemble U) (f : U -> V) (y : V),
  y ∈ Im U V A f <-> exists x : U, x ∈ A /\ f x = y.
Proof.
  intros U V A f y. split; intros H1.
  - apply Im_inv in H1. auto.
  - destruct H1 as [x [H1 H2]]. apply Im_intro with (x := x); auto.
Qed.

Lemma Power_set_Add :
  forall (U : Type) (A : Ensemble U) (h : U),
    Power_set (Add U A h) =
    Union (Ensemble U)
      (Power_set A)
      (Im (Ensemble U) (Ensemble U) (Power_set A) (fun S => Add U S h)).
Proof.
  intros U A h. apply set_equal_def. intros x. split; intros H1.
  - rewrite In_Power_set_def in H1. rewrite In_Union_def. destruct (classic (h ∈ x)) as [H2 | H2].
    -- right. rewrite In_Im_def. exists (x − ⦃h⦄). split.
       * unfold Add in H1. apply In_Power_set_def. apply Subset_def. intros y H3. apply In_Setminus_def in H3 as [H3 H4].
         rewrite Subset_def in H1. specialize (H1 y H3). autoset.
       * unfold Add in *. rewrite Subset_def in H1. apply set_equal_def. intros y. split; intros H3.
         + specialize (H1 y). apply In_Union_def in H3 as [H3 | H3]; try autoset. apply In_singleton_def in H3. autoset.
         + apply In_Union_def. destruct (classic (y = h)) as [H4 | H4]. right. apply In_singleton_def; auto. left. apply In_Setminus_def. split; autoset.
    -- left. apply In_Power_set_def. apply Subset_def. intros y H3. rewrite Subset_def in H1. specialize (H1 y H3). unfold Add in H1. 
       apply In_Union_def in H1 as [H1 | H1]; autoset. apply In_singleton_def in H1. subst. contradiction.
  - rewrite In_Power_set_def. apply In_Union_def in H1 as [H1 | H1].
    -- unfold Add. apply Subset_def. intros y H2. rewrite In_Power_set_def in H1. autoset.
    -- rewrite In_Im_def in H1. destruct H1 as [S [H1 H2]]. unfold Add in *. rewrite In_Power_set_def in H1. rewrite set_equal_def in H2. 
       apply Subset_def. intros y H3. specialize (H2 y). destruct H2 as [H2 H4]. specialize (H4 H3). autoset.
Qed.

Lemma Add_Union_assoc : forall (U : Type) (A B : Ensemble U) (h : U),
  Add U (A ⋃ B) h = (Add U A h) ⋃ B.
Proof.
  unfold Add. autoset.
Qed.

Lemma cardinal_Union : forall (U : Type) (A B : Ensemble U) (n m : ℕ),
  |A| = n -> |B| = m -> A ⋂ B = ∅ -> |A ⋃ B| = n + m.
Proof.
  intros U A B n m H1 H2 H3. induction H1 as [| A n H1 IH x H4].
  - rewrite Union_Identity. simpl. auto.
  - assert (H5 : A ⋂ B = ∅). { rewrite <- H3. unfold Add in *. apply set_equal_def. intros y. split; intros H5; autoset. rewrite H3 in H5. contradiction. }
    specialize (IH H5). rewrite <- Add_Union_assoc. apply card_add; auto. intros H6. apply H4. unfold Add in *. apply In_Union_def in H6 as [H6 | H6]; autoset.
    rewrite set_equal_def in H3. specialize (H3 x) as [H3 H7]. assert (x ∈ (A ⋃ ⦃x⦄) ⋂ B) as H8 by autoset. specialize (H3 H8). contradiction. 
Qed.

Lemma h_not_in_Power_set_A : forall (U : Type) (A : Ensemble U) (h : U),
  h ∉ A -> forall x, x ∈ ℙ(A) -> h ∉ x.
Proof.
  intros U A h H1 x H2. rewrite In_Power_set_def in H2. autoset.
Qed.

Lemma Add_not_in_preserves_cardinality : forall (U : Type) (A : Ensemble (Ensemble U)) (h : U) (n : ℕ),
  (forall x, x ∈ A -> h ∉ x) -> |A| = n -> |(Im (Ensemble U) (Ensemble U) A (fun S : Ensemble U => Add U S h))| = n.
Proof.
  intros U A h n H1 H2. induction H2 as [| A n H2 IH x H3].
  - rewrite image_empty. apply card_empty.
  - rewrite Im_add. apply card_add; auto. apply IH. intros y H4. apply H1. unfold Add. autoset.
    intros H4. apply In_Im_def in H4 as [S [H4 H5]]. specialize (H1 S) as H6. assert (S ∈ Add (Ensemble U) A x) as H7. { unfold Add. autoset. }
    specialize (H6 H7). clear H7. specialize (H1 x). assert (x ∈ Add (Ensemble U) A x) as H7. { unfold Add. autoset. }
    specialize (H1 H7). clear H7. destruct Empty_or_exists_In with (U := U) (A := S) as [H7 | [y H7]]; destruct Empty_or_exists_In with (U := U) (A := x) as [H8 | [z H8]]; autoset.
    -- rewrite set_equal_def in H5. specialize (H5 z) as [H5 H9]. assert (H10 : z ∈ Add U x h) by (unfold Add; autoset). specialize (H9 H10). unfold Add in H9.
       rewrite Union_Identity in H9. apply In_singleton_def in H9. autoset.
    -- rewrite set_equal_def in H5. specialize (H5 y) as [H5 H9]. assert (H10 : y ∈ Add U S h) by (unfold Add; autoset). specialize (H5 H10). unfold Add in H5.
       rewrite Union_Identity in H5. apply In_singleton_def in H5. autoset.
    -- destruct (classic (x = S)) as [H9 | H9]; autoset. apply H9. unfold Add in H5. rewrite set_equal_def in H5. apply set_equal_def. intros w; split; intros H10.
       specialize (H5 w) as [H5 H11].  assert (H12 : w ∈ Add U x h) by (unfold Add; autoset). specialize (H11 H12). apply In_Union_def in H11 as [H11 | H11]; autoset.
       apply In_singleton_def in H11. subst. contradiction. specialize (H5 w) as [H5 H11]. assert (H12 : w ∈ Add U S h) by (unfold Add; autoset). specialize (H5 H12).
       apply In_Union_def in H5 as [H5 | H5]; autoset. apply In_singleton_def in H5. subst. contradiction. 
Qed.

Lemma Power_set_Image_Add_preserves_cardinality : forall (U : Type) (A : Ensemble U) (n : ℕ) (h : U),
  h ∉ A -> |ℙ(A)| = n -> |Im (Ensemble U) (Ensemble U) (ℙ(A)) (fun S : Ensemble U => Add U S h)| = n.
Proof.
  intros U A n h H1 H2. apply Add_not_in_preserves_cardinality. apply h_not_in_Power_set_A; auto. auto.
Qed.

Lemma cardinal_Power_set_add : forall (U : Type) (A : Ensemble U) (h : U) (n : ℕ),
  |ℙ(A)| = n -> h ∉ A -> |ℙ(Add U A h)| = 2 * n.
Proof.
  intros U A h n H1 H2. rewrite Power_set_Add. apply cardinal_Union; auto. rewrite Nat.add_0_r. apply Power_set_Image_Add_preserves_cardinality; auto.
  apply set_equal_def. intros x. split; intros H3; autoset. apply In_Intersection_def in H3 as [H3 H4]; autoset. rewrite In_Power_set_def in H3.
  apply In_Im_def in H4 as [S [H4 H5]]. rewrite In_Power_set_def in H4. unfold Add in H5. autoset. rewrite Subset_def in H4, H3. specialize (H4 h). specialize (H3 h).
  assert (H5 : h ∈ S ⋃ ⦃h⦄) by autoset. specialize (H3 H5). contradiction.
Qed.

Proposition prop_14_6 : forall (U : Type) (A : Ensemble U) (n : ℕ),
  Finite_set A -> |A| = n -> |ℙ(A)| = 2^n.
Proof.
  intros U A n [l H1] H2. generalize dependent A. generalize dependent n. induction l as [| h t IH].
  - intros n A H1 H2. rewrite list_to_ensemble_nil in H1. rewrite <- H1 in H2.
    apply cardinal_Empty in H2. subst. simpl. rewrite Power_set_Empty_1. apply cardinal_Singleton.
  - intros n A H1 H2. rewrite list_to_ensemble_cons in H1. rewrite <- H1 in H2.
    destruct (classic (h ∈ list_to_ensemble t)) as [H3 | H3].
    -- assert (Add _ (list_to_ensemble t) h = list_to_ensemble t) as H4.
       {
          apply set_equal_def. intros x. unfold Add. split; intros H4; try autoset.
          apply In_Union_def in H4 as [H4 | H4]; auto. apply In_singleton_def in H4. autoset.
       }
       rewrite H1 in H2. apply IH; auto. rewrite <- H1. unfold Add in H4. rewrite Union_comm in H4. autoset.
    -- assert (cardinal (Ensemble U) (Power_set (list_to_ensemble t)) (2 ^ (n-1))) as H4.
       {
          apply IH; auto. replace (list_to_ensemble t) with (A − ⦃h⦄). 
          2 : { apply set_equal_def. intros x. rewrite <- H1. split; intros H4. try autoset. apply In_Setminus_def. split; repeat autoset. }
          apply cardinal_minus; autoset. destruct n as [| n']. apply cardinal_Empty_1 in H2. rewrite set_equal_def in H2. specialize (H2 h) as [H2 H5].
          assert (H6 : h ∈ ⦃h⦄ ⋃ list_to_ensemble t) by autoset. specialize (H2 H6). contradiction.
          replace (S (S n' - 1)) with (S n') by lia. auto.
        }
        replace (⦃h⦄ ⋃ list_to_ensemble t) with (Add _ (list_to_ensemble t) h) in H2. 2 : {  unfold Add; autoset. }
        assert (H5 : cardinal (Ensemble U) (Power_set (Add U (list_to_ensemble t) h)) (2 * (2 ^ (n - 1)))).
        { apply cardinal_Power_set_add; auto. } assert (H6 : Add U (list_to_ensemble t) h = A). { rewrite <- H1. unfold Add. autoset. }
        assert (n = 0 \/ n > 0) as [H7 | H7] by lia.
        + subst. apply cardinal_Empty_1 in H2. rewrite set_equal_def in H2. specialize (H2 h) as [H1 H2].
          assert (H7 : h ∈ Add U (list_to_ensemble t) h). { unfold Add. autoset. } specialize (H1 H7). contradiction.
        + rewrite H6 in H5. replace (2 * (2 ^ (n - 1))) with (2 ^ n) in H5. 2 : { replace n with (S (n - 1)) at 1 by lia. rewrite Nat.pow_succ_r'. lia. }
          auto. 
Qed.

Check prop_14_6.

Open Scope nat_scope.

Lemma lemma_14_1 : forall n : nat,
  n >= 7 -> fact n > 3^n.
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  assert (S k = 7 \/ k >= 7) as [H2 | H2] by lia.
  - rewrite H2. compute; lia.
  - simpl in *. nia.
Qed.

Lemma lemma_14_2 : forall n : nat,
  n >= 6 -> fact n > n^3.
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  - assert (S k = 6 \/ k >= 6) as [H2 | H2] by lia.
    + rewrite H2. compute. lia.
    + rewrite fact_simpl. specialize (IH H2). simpl in *. nia.
Qed.

Lemma lemma_14_3 : forall n : nat,
  3^n >= n^3.
Proof.
  induction n as [| k IH]; try (simpl; nia).
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k > 3) as [H1 | [H1 | [H1 | [H1 | H1]]]] by lia; try (subst; simpl; nia).
  replace (3 ^ S k) with (3 ^ k + 3^k + 3^k) by (simpl; lia). replace (S k ^ 3) with (k^3 + 3 * k^2 + 3 * k + 1) by (simpl; lia).
  assert (H2 : 3^k >= k * k^2). { replace (k * k^2) with (k^3) by (simpl; lia). auto. }
  assert (H3 : 3^k >= 3 * k^2). { nia. } assert (H4 : 3^k >= k * k * k). { replace (k * k * k) with (k^3) by (simpl; lia). auto. }
  assert (H5 : 3^k >= 3 * k + 1). { nia. } nia.
Qed.

Lemma lemma_14_4 : forall (l : list Prop),
  ~ (fold_right and True l) <-> fold_right or False (map (fun P => ~ P) l).
Proof.
  intros l. split.
  - intro H1. induction l as [| h t IH].
    -- simpl in H1. exfalso. apply H1. apply I.
    -- rewrite map_cons. replace ((~ h) :: map (fun P : Prop => ~ P) t) with ([~ h] ++ map (fun P : Prop => ~ P) t) by reflexivity.
       rewrite fold_right_app. simpl. replace (h :: t) with ([h] ++ t) in H1 by reflexivity. rewrite fold_right_app in H1. simpl in H1.
       apply not_and_or in H1 as [H2 | H2]. left. auto. right. apply (IH H2).
  - intro H1. induction l as [| h t IH].
    -- simpl. auto.
    -- simpl in *. destruct H1 as [H1 | H1]. apply or_not_and. left. auto. apply or_not_and. right. apply IH; auto.
Qed.

Open Scope R_scope.

Lemma lemma_14_5 : forall (l : list R),
  Rabs (sum_f 0 (length l - 1) (fun i => nth i l 0)) <= sum_f 0 (length l - 1) (fun i => Rabs (nth i l 0)).
Proof.
  induction l as [| h t IH].
  - simpl. repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
    -- rewrite H1. repeat rewrite sum_f_0_0; solve_abs.
    -- rewrite sum_f_nth_cons_7; try lia. rewrite sum_f_nth_cons_5; try lia. solve_abs.
Qed.

Module Fibonacci.

  Fixpoint fibonacci_nat (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fibonacci_nat(n') + fibonacci_nat(n'')
            end
  end.

  Fixpoint fibonacci_R (n : nat) : R :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fibonacci_R(n') + fibonacci_R(n'')
            end
  end.

  Local Notation F := fibonacci_R.

  Lemma fib_S_S_n : forall n : nat, F (S (S n)) = F (S n) + F n.
  Proof.
    reflexivity.
  Qed.

  Lemma fib_n_plus_2 : forall n : nat, F(n+2) = F(n+1) + F(n).
  Proof.
    intro n. 
    replace ( (n + 1)%nat ) with ( S n )%nat by lia.
    replace ( (n + 2)%nat ) with ( S (S n) )%nat by lia.
    apply fib_S_S_n.
  Qed.

  Lemma fib_n_plus_1 : forall n : nat, (n > 0)%nat -> F(n+1) = F(n) + F(n-1).
  Proof.
    intros n H1. destruct n as [| n'] eqn:En.
    - simpl. exfalso. apply (Nat.lt_irrefl) in H1. apply H1.
    - replace ( (S n') ) with ( (n' + 1)%nat ) by lia. 
      rewrite <- Nat.add_assoc. simpl.
      replace ( (n' + 1 - 1)%nat ) with ( n' ) by lia.
      apply fib_n_plus_2.
  Qed.

  Lemma fib_n_plus_3 : forall n : nat, F(n+3) = F(n+2) + F(n+1).
  Proof.
    intro n. 
    replace ( (n + 2)%nat ) with ( (n + 1 + 1)%nat ) by lia.
    replace ( (n + 3)%nat ) with ( (n + 1 + 2)%nat ) by lia.
    apply fib_n_plus_2.
  Qed.

  Lemma fib_n : forall n, 
    (n > 1)%nat -> F n = F (n - 1) + F (n - 2).
  Proof.
    intros n H1. replace n with (S (S (n - 2))) at 1 by lia. 
    replace (n - 1)%nat with (S (n - 2)) by lia. apply fib_S_S_n.
  Qed.

  Open Scope nat_scope.

  Lemma strong_induction :
    forall P : nat -> Prop,
    (forall m, (forall k : nat, k < m -> P k) -> P m) ->
    forall n, P n.
  Proof.
    intros P H1 n. assert (H2: forall k, k <= n -> P k).
    - induction n.
      -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
      -- intros k Hk. apply H1. intros k' Hk'. apply IHn. lia.
    - apply H2. lia.
  Qed.

  Close Scope nat_scope.

  Lemma fib_n_ge_1 : forall n, F n >= 1.
  Proof.
    apply strong_induction.
    intros n IH. destruct n as [| n'] eqn:En.
    - simpl. lra.
    - destruct n' as [| n''] eqn:En'.
      -- simpl. lra.
      -- assert (H1 : F (S n'') >= 1) by (apply IH; lia).
        assert (H2 : F n'' >= 1) by (apply IH; lia).
        rewrite fib_S_S_n.
        lra.
  Qed.

  Lemma fib_n_gt_0 : forall n, F n > 0.
  Proof.
    intros n. assert (H1 : F n >= 1) by apply fib_n_ge_1. lra.
  Qed.

  Lemma fib_Sn_ge_fib_n : forall n : nat,
    F (S n) >= F n.
  Proof.
    induction n as [| k IH].
    - simpl. lra.
    - rewrite -> fib_S_S_n.  
      assert (H1 : F (S k) > 0) by apply fib_n_gt_0.
      assert (H2 : F k > 0) by apply fib_n_gt_0.
      lra.
  Qed.

  Lemma n_ge_1_imp_fib_Sn_gt_fib_n : forall n : nat,
    (n >= 1)%nat -> F (S n) > F n.
  Proof.
    intros n H. destruct n as [| n'] eqn:En.
    - lia.
    - rewrite -> fib_S_S_n. 
      assert (H1 : F (S n') > 0) by apply fib_n_gt_0.
      assert (H2 : F n' > 0) by apply fib_n_gt_0.
      lra.
  Qed.

  Lemma n1_ge_n2_imp_fib_n1_ge_fib_n2 : forall (n1 n2 : nat),
    (n1 >= n2)%nat -> F n1 >= F n2.
  Proof.
    intros n1 n2 H.
    induction H.
    - lra.
    - assert (H2 : F (S m) >= F m)  by apply fib_Sn_ge_fib_n.
      lra.
  Qed.

  Lemma fib_n_ge_n : forall n : nat,
    F n >= INR n.
  Proof.
    induction n as [| k IH].
    - simpl. lra.
    - replace ( (S k) ) with ( (k + 1)%nat ) by lia.
      destruct k as [| k'] eqn:Ek.
      -- simpl. lra.
      -- rewrite fib_n_plus_1.
        --- rewrite plus_INR. 
            assert (H1 : F (S k' - 1) >= 1) by apply fib_n_ge_1.
            replace ( (INR 1) ) with ( (1) ) by (simpl; lra). lra.
        --- lia.
  Qed.
      
  Lemma fib_2n_ge_fib_n : forall n : nat,
    F (2 * n) >= F n.
  Proof.
    intros n. assert (H : (2 * n >= n)%nat) by lia.
    apply n1_ge_n2_imp_fib_n1_ge_fib_n2. apply H.
  Qed.

  Lemma fib_2n_times_fib_n_ge_n : forall n : nat,
    F (2 * n) * F (2 * n - 1) >= F n.
  Proof.
    intro n. assert (H1 : F ((2 * n)%nat) > 0) by apply fib_n_gt_0.
    assert (H2 : F ((2 * n - 1)%nat) >= 1) by apply fib_n_ge_1.
    assert (H3 : F ((2 * n)%nat) >= F n) by apply fib_2n_ge_fib_n.
    apply Rmult_ge_compat_l with (r := F (2 * n)%nat) in H2.
    - rewrite Rmult_1_r in H2. lra.
    - apply Rgt_ge. apply H1. 
  Qed.

  Lemma fib_prod_ge_n : forall (n : nat),
    F (2 * n) * F (2 * n - 1) >= INR n.
  Proof.
    intros n. 
    assert (H1 : F (2 * n) * F (2 * n - 1) >= F n) by apply fib_2n_times_fib_n_ge_n.
    assert (H2 : F n >= INR n) by apply fib_n_ge_n.
    apply Rge_trans with (r3 := INR n) in H1.
    - apply H1.
    - apply H2.
  Qed.
  
End Fibonacci.

Section section_14_6.

  Import Fibonacci.

  Local Notation F_nat := fibonacci_nat.
  Local Notation F := fibonacci_R.

  Compute (map F_nat (seq 0 15)).

  Lemma lemma_14_6_b : forall n : nat,
    sum_f 0 n (fun i => F i) = F (S (S n)) - 1.
  Proof.
    intros n. induction n as [| k IH].
    - rewrite sum_f_0_0. simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. repeat rewrite fib_S_S_n. lra.
  Qed.

  Lemma lemma_14_6_c : forall n : nat,
    sum_f 0 n (fun i => (F i)^2) = F n * F (S n).
  Proof.
    induction n as [| k IH].
    - rewrite sum_f_0_0. simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. replace (F (S k) ^ 2) with (F (S k) * F (S k)) by lra. 
      repeat rewrite fib_S_S_n. lra.
  Qed.
  
End section_14_6.

Section section_14_7.
  Import Fibonacci.

  Local Notation F := fibonacci_R.

  Lemma lemma_14_7 : forall n : nat,
    (n >= 13)%nat -> F n > INR (n)^2.
  Proof.
    intros n H1. induction n as [| k IH]; try lia.
    assert (S k = 13 \/ k >= 13)%nat as [H2 | H2] by lia.
    - rewrite H2. compute; lra.
    - specialize (IH H2). rewrite fib_n in IH; try lia. rewrite fib_n; try lia. rewrite fib_n; try lia.
      replace (S k - 1 - 1)%nat with (k - 1)%nat by lia. replace (S k - 2)%nat with (k-1)%nat by lia.
      replace (S k - 1 - 2)%nat with (k - 2)%nat by lia. replace (INR (S k) ^ 2) with (INR k ^ 2 + 2 * INR k + 1).
      2 : { break_INR. simpl. nra. } assert (H4 : F (k - 1) = F (k - 2) + F (k - 3)). 
      { set (n := (k - 1)%nat). replace (k - 2)%nat with (n - 1)%nat by lia. replace (k - 3)%nat with (n - 2)%nat by lia. apply fib_n; lia. }
      assert (H5 : F (k - 1) >= F (k - 2)). { apply n1_ge_n2_imp_fib_n1_ge_fib_n2; lia. }
      assert (H6 : F (k - 2) >= F (k - 3)). { apply n1_ge_n2_imp_fib_n1_ge_fib_n2; lia. }
      assert (H7 : F (k - 1) >= (INR k ^ 2) / 2). { nra. } assert (H8 : INR k >= 13). { apply le_INR in H2. simpl in H2; nra. } nra. 
  Qed.
  
End section_14_7.