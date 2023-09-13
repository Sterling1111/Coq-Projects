Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Foundations Require Export Tactics.

Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof.
  simpl. reflexivity.
Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true : plus_claim.
Proof.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop := n = 3.

Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) := 
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  unfold injective. intros. injection H as H1. apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros. split.
  - apply H.
  - apply H0.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split.
  - destruct n as [| n'].
    * reflexivity.
    * simpl in H. discriminate H.
  - destruct m.
    * reflexivity.
    * rewrite add_comm in H. simpl in H. discriminate H.
Qed.

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros.
  destruct H as [H1 H2].
  rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Lemma and_example2' : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2].
  rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros.
  apply and_exercise in H.
  destruct H as [H1 H2].
  rewrite H1. simpl. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  destruct H as [H1 _].
  apply H1.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ H2].
  apply H2.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2]. split.
  - apply H2.
  - apply H1.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [H1 [H2 H3]]. split.
  - split.
    * apply H1.
    * apply H2.
  - apply H3.
Qed.

Check and : Prop -> Prop -> Prop.
Check or : Prop -> Prop -> Prop.

Lemma factor_is_O : forall n m : nat,
  n = O \/ m = 0 -> n * m = 0.
Proof.
  intros n m [H1 | H2].
  - rewrite -> H1. simpl. reflexivity.
  -  rewrite -> H2. apply mul_comm.
Qed.

Lemma or_intro_l : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros.
  left.
  apply H.
Qed.

Lemma zero_or_succ : forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - left. reflexivity.
  - right. simpl. reflexivity. 
Qed.

Lemma mult_is_O : forall n m : nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros. 
  destruct n as [| n'].
  - left. reflexivity.
  - destruct m as [| m'].
    * right. reflexivity.
    * simpl in H. discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [H1 | H2].
  - right. apply H1.
  - left. apply H2.
Qed.

Module NotPlayground.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

Theorem not_implies_our_not' : forall P Q : Prop,
  ~P -> (P -> Q).
Proof.
  intros. unfold not in H. destruct H. apply H0.
Qed.


(*destruct on A -> B will assume B, but we will then need to show A*)
Theorem not_implies_our_not : forall P : Prop,
  ~P -> (forall Q : Prop, P -> Q).
Proof.
  unfold not. intros. destruct H. apply H0.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intro H. discriminate H.
Qed.

Theorem not_False : ~False.
Proof.
  unfold not. intro H. destruct H.
Qed.

Theorem true_and_false : forall P : Prop,
  (P /\ ~P) -> False.
Proof.
  intros P [H1 H2]. unfold not in H2. destruct H2. apply H1. 
Qed.

Theorem contradiction_implies_anything' : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H. apply true_and_false in H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2].
  unfold not in H2. destruct H2. apply H1.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros. unfold not. intro H2. destruct H2. apply H.
Qed.

(*Let P be any proposition and suppose P. We must show that this implies ~~P
  By definition we are to show that (P->False) -> False. Suppose P -> False, If
  we had P then we would be supposing false. Lets suppose we can get P somehow and
  take false. Then what we want to show which is false is shown by vacuous truth. now
  show P from our original hypothesis. Qed*)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2.
  unfold not. unfold not in H2. intro H3. apply H2. apply H1. apply H3.
Qed.

Theorem not_both_true_and_false : forall P Q : Prop,
  ~(P /\ ~P).
Proof.
  intros. unfold not. intros [H1 H2]. destruct H2. apply H1.
Qed.

(* the best way to give an informal proof would be a simpl truth table*)

 Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~P /\ ~Q.
 Proof.
  intros P Q H. unfold not in H. split.
  - unfold not. intro H2. destruct H. left. apply H2.
  - unfold not. intro H2. destruct H. right. apply H2.
 Qed.

 Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
 Proof.
  intros.
  destruct b.
  - unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity.
 Qed.

 Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
 Proof.
  intros.
  destruct b.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity.
 Qed.
 
Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n : nat) : Prop := 
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n : nat,
  ~ (O = S n).
Proof.
  intros n H.
  assert (H2 : disc_fn O). {simpl. apply I. }
  rewrite -> H in H2. simpl in H2. apply H2.
Qed.

Module IffPlayground.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End IffPlayground.


Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.


Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. unfold not. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intro H. split.
    * destruct H as [H2 | H3].
      + left. apply H2.
      + destruct H3 as [H2 H3]. right. apply H2.
    * destruct H as [H2 | H3].
      + left. apply H2.
      + destruct H3 as [H4 H5]. right. apply H5.
  - intro H. destruct H as [[H2 | H3] [H4 | H5]].
    * left. apply H2.
    * left. apply H2.
    * left. apply H4.
    * right. split.
      + apply H3.
      + apply H5.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

Definition Even (x : nat) : Prop := exists n : nat, x = double n.
Definition Odd (x : nat) : Prop := exists n : nat, x = S (double n).

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. simpl. reflexivity.
Qed.

Theorem exists_example_2 : forall n : nat,
  (exists m : nat, n = 4 + m) -> (exists o : nat, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m). simpl in Hm. simpl. apply Hm. 
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros X P H1. 
  unfold not. intro H2. destruct H2 as [x H2]. 
  destruct H2. apply H1.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x1 H]. destruct H as [H | H].
    * left. exists (x1). apply H.
    * right. exists (x1). apply H.
  - intros H. destruct H as [H | H].
    * destruct H as [x1 H]. exists (x1). left. apply H.
    * destruct H as [x1 H]. exists (x1). right. apply H.
Qed.

(*Lemma plus_minus_assoc : forall n m : nat,
  n <=? m = true -> n + (m - n) = (n + m) - n.
Proof.
  
Qed.*)

Theorem leb_plus_exists : forall n m : nat,
  n <=? m = true -> exists x, m = n + x.
Proof.
  intros. exists (m - n). generalize dependent n.
  induction m as [| k IH].
  - destruct n as [| n']. 
    * simpl. reflexivity.
    * simpl. discriminate.
  - destruct n as [| n'].
    * simpl. reflexivity.
    * simpl. intros H. f_equal. apply IH. apply H.
Qed.

Lemma leb_n_plus : forall n m : nat,
  n <=? n + m = true.
Proof.
  intros n m.
  induction n as [| k IH].
  - simpl. reflexivity.
  - rewrite add_comm. rewrite <- plus_n_Sm. simpl. rewrite add_comm. apply IH.
Qed.

Theorem plus_exists_leb : forall n m : nat,
  (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n m [x H].
  rewrite -> H. destruct x as [| x'].
  - rewrite -> add_0_r. apply leb_refl.
  - rewrite -> add_comm. simpl. destruct x' as [| x''].
    * simpl. apply NatList.leb_n_Sn.
    * simpl. rewrite -> add_comm. rewrite plus_n_Sm. rewrite plus_n_Sm. apply leb_n_plus.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | h :: t => h = x \/ In x t
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| h t IH].
  - simpl. intros [].
  - simpl. intros [H | H].
    * left. rewrite -> H. reflexivity.
    * right. apply IH. apply H. 
Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros. induction l as [| h t IH].
  - simpl. split. 
    * intros [].
    * intros [x [H1 []]].
  - split. 
    * simpl. intros [H | H].
      + exists h. split.
        -- apply H.
        -- left. reflexivity.
      + apply IH in H. destruct H as [x' [H1 H2]]. exists x'. split.
        -- apply H1.
        -- right. apply H2.
    * simpl. intros [x [H1 [H2 | H3]]]. 
      + left. rewrite <- H1. rewrite -> H2. reflexivity.
      + right. apply IH. exists x. split.
        -- apply H1.
        -- apply H3.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros. split.
    * simpl. intros H. right. apply H.
    * simpl. intros [[] | H].
      + apply H.
  - intros. simpl. split.
    * intros [H | H].
      + left. left. apply H.
      + rewrite <- or_assoc. right. apply IH. apply H.
    * intros [[H | H] | H].
      + left. apply H.
      + right. apply IH. left. apply H.
      + right. apply IH. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_in : forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros. induction l as [| h t IH].
  - split.
    * simpl. intros H. apply I.
    * simpl. intros H1 x H2. apply ex_falso_quodlibet. apply H2.
  - simpl. split.
    * intros H. split.
      + apply H. left. reflexivity.
      + apply IH. intros x H2. apply H. right. apply H2.
    * intros [H1 H2] x [H3 | H4].
      + rewrite -> H3 in H1. apply H1.
      + apply iff_sym in IH. assert (H5 : (forall x : T, In x t -> P x)).
        { apply IH. apply H2. }
        apply H5. apply H4.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (fun n => if odd n then Podd n else Peven n).

Theorem combine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat),
  (odd n = true -> Podd n) -> 
  (odd n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even. destruct (odd n).
  - apply H1. reflexivity.
  - apply H2. reflexivity. 
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = true -> Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1. rewrite H2 in H1. apply H1. 
Qed.

Theorem combine_odd_even_elim_even : forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = false -> Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1. rewrite -> H2 in H1. apply H1.
Qed.

Check plus : nat -> nat -> nat.
Check add_comm : forall n m : nat, n + m = m + n.

Lemma add_comm3 : forall x y z,
  x + (y + z) = (z + y) + x.
Proof.
  intros.
  rewrite -> add_comm.
  rewrite -> add_comm.
Abort.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42 l).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 : 
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. simpl. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | h :: t => rev_append t (h :: l2)
  end.
  
Definition tr_rev {X : Type} (l : list X) : list X := 
  rev_append l [].

Lemma rev_append_lem : forall (X : Type) (l1 l2 l3 : list X),
  rev_append l1 (l2 ++ l3) = (rev_append l1 l2) ++ l3.
Proof.
  intros. generalize dependent l2.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. intros l2. rewrite <- IH. simpl. reflexivity.
Qed.

Theorem tr_rev_correct' : forall (X : Type) (l : list X),
  tr_rev l = rev l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - unfold tr_rev. simpl. rewrite <- IH. unfold tr_rev.
    Set Printing Parentheses. replace (rev_append t [h]) with (rev_append t ([] ++ [h])).
    * apply rev_append_lem.
    * simpl. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intro X. apply functional_extensionality. intro x. rename x into l.
  unfold tr_rev. induction l as [| h t IH].
  - simpl. reflexivity.
  - unfold tr_rev. simpl. rewrite <- IH. unfold tr_rev.
  Set Printing Parentheses. replace (rev_append t [h]) with (rev_append t ([] ++ [h])).
  * apply rev_append_lem.
  * simpl. reflexivity.
Qed.

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. simpl. reflexivity. Qed.

Lemma negb_b_is_not_b : forall b : bool,
  negb b = true -> b = false.
Proof.
  intros b H. destruct b. simpl in H. 
  - apply symmetry. apply H.
  - reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  induction k as [| k' IH].
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  induction n as [| n' IH].
  - simpl. exists 0. simpl. reflexivity.
  - destruct (even (S n')) eqn:E1. rewrite -> even_S in E1. apply negb_b_is_not_b in E1.
    * destruct (even n') eqn:E2 in IH.
      + rewrite-> E1 in E2. discriminate E2.
      + destruct IH as [x IH]. exists (S x). rewrite -> IH. simpl. reflexivity.
    * destruct (even n') eqn:E2.
      + destruct IH as [x IH]. exists x. rewrite -> IH. reflexivity.
      + rewrite <- E2 in E1. rewrite even_S in E1. rewrite E2 in E1. simpl in E1. 
        discriminate E1.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intro n. split.
  - intro H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. unfold Even. exists k. reflexivity.
  - unfold Even. intros [k H]. rewrite H. apply even_double.  
Qed.

Theorem Even_plus_Even : forall (n m : nat),
  Even n /\ Even m -> Even (n + m).
Proof.
  intros n m. unfold Even. intros [[x1 H1] [x2 H2]].
  rewrite -> H1. rewrite -> H2. exists (x1 + x2). rewrite -> double_plus.
  rewrite -> double_plus. rewrite -> add_assoc. rewrite -> add_comm.
  rewrite <- add_assoc. rewrite -> add_assoc. replace (x1 + x2) with (x2 + x1).
  - rewrite <- double_plus. reflexivity.
  - apply add_comm.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - intros H. apply eqb_true in H. apply H.
  - intros H. rewrite -> H. apply eqb_refl.
Qed.

Fail Definition is_even_prime n := 
  if n = 2 then true
  else false.

Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. simpl. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof. reflexivity. Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not. simpl. intro H. discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1 eqn:E1 in H.
    * simpl in H. rewrite H. rewrite E1. split.
      + reflexivity.
      + reflexivity.
    * simpl in H. discriminate H.
  - intros [H1 H2]. rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H. unfold not. rewrite <- not_true_iff_false in H.
    unfold not in H. intros H2. apply H. rewrite <- eqb_eq in H2.
    apply H2.
  - unfold not. intros H. rewrite <- not_true_iff_false.  unfold not.
    intros H2. apply H. apply eqb_eq in H2. apply H2.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1 with
  | nil => match l2 with 
           | nil => true
           | _ => false
           end
  | h1 :: t1 => match l2 with
              | nil => false
              | h2 :: t2 => andb (eqb h1 h2) (eqb_list eqb t1 t2)
              end
end.

Lemma andb_a_b_true : forall b1 b2 : bool,
  b1 = true /\ b2 = true -> andb b1 b2 = true.
Proof.
  intros b1 b2 [H1 H2].
  - rewrite -> H1. rewrite -> H2. simpl. reflexivity.
Qed.

Theorem eqb_list_true_iff : 
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros. split.
  - intros H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
    * simpl in H. destruct l2 eqn:E1 in H.
      + symmetry. apply E1.
      + rewrite E1. simpl. discriminate.
    * simpl. destruct l2 eqn:E1.
      + discriminate.
      + intros H2. f_equal.
        -- apply H. rewrite andb_commutative in H2. apply andb_true_elim2 in H2. apply H2.
        -- apply IH. apply andb_true_elim2 in H2. apply H2.
  - generalize dependent l2. induction l1 as [| h1 t1 IH].
    * intros l2 H2. destruct l2 eqn:E1.
      + simpl. reflexivity.
      + rewrite <- H2. simpl. reflexivity.
    * intros l2 H2. rewrite <- H2. simpl. apply andb_a_b_true. split.
      + apply H. reflexivity. 
      + apply IH. reflexivity.
Qed.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
  - intro H. induction l as [| h t IH].
    * simpl. apply I.
    * simpl. split.
      + simpl in H. destruct (test h) eqn:E1 in H.
        -- apply E1.
        -- discriminate H.
      + apply IH. simpl in H. destruct (test h) eqn:E1 in H.
        -- apply H.
        -- discriminate H.
  - intro H. induction l as [| h t IH].
    * simpl. reflexivity.
    * simpl. destruct (test h) eqn:E1.
      + apply IH. simpl in H. destruct H as [H1 H2]. apply H2.
      + rewrite <- E1. simpl in H. destruct H as [H1 H2]. apply H1.
Qed.

Print forallb_true_iff.

Definition excluded_middle := forall P : Prop,
  P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. unfold not. intros H2. discriminate H2.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m)(n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~ ~ (P \/ ~P).
Proof.
  intros P. unfold not. intros H. apply H. right.
  intro H2. apply H. left. apply H2.
Qed.

Theorem not_exists_dist : 
  excluded_middle -> 
  forall (X : Type) (P : X -> Prop),
  ~ (exists x, ~ P x) -> (forall x , P x).
Proof.
  unfold not. intros H1 X P H2 x. unfold excluded_middle in H1.
  destruct H1 with (P := P x) as [H3 | H3]. apply H3. destruct H2.
  exists x. unfold not in H3. apply H3.
Qed.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition double_negation_elimination := forall P : Prop,
  ~ ~P -> P.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Theorem exluded_middle_imp_de_morgan_not_and_not : excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not. unfold not.
  intros H1 P Q H2. destruct H1 with (P := P).
  - left. apply H.
  - right. destruct H1 with (P := Q).
    * apply H0.
    * destruct H2. split.
      + apply H.
      + apply H0.
Qed.

Theorem de_morgan_not_and_not_imp_double_negation_elimination :
  de_morgan_not_and_not -> double_negation_elimination.
Proof.
  unfold de_morgan_not_and_not. unfold double_negation_elimination. unfold not.
  intros H1 P H2. destruct (H1 P False).
  - intros H3.  destruct H3 as [H3 H4]. apply H2. apply H3.
  - apply H.
  - destruct H.
Qed.

Theorem double_negation_elimination_imp_implies_to_or :
  double_negation_elimination -> implies_to_or.
Proof.
  unfold double_negation_elimination. unfold implies_to_or. unfold not.
  intros H1 P Q H2. destruct (H1 ((P -> False) \/ Q)) as [H3 | H3].
  - intro H3. apply H3. right. apply H2. apply H1. intro H4. apply H3. left. apply H4.
  - left. apply H3.
  - right. apply H3.
Qed.

Theorem implies_to_or_imp_excluded_middle : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. unfold excluded_middle. unfold not.
  intros H1 P. destruct (H1 P P) as [H2 | H2].
  - intro H2. apply H2.
  - right. apply H2.
  - left. apply H2.
Qed.

Theorem double_negation_elimination_imp_peirce : 
  double_negation_elimination -> peirce.
Proof.
  unfold double_negation_elimination. unfold peirce. unfold not.
  intros H1 P Q H2. apply H1. intros H3. apply H3. apply H2. intros H4. 
  destruct H3. apply H4.
Qed.

Theorem peirce_imp_double_negation_elimination : 
  peirce -> double_negation_elimination.
Proof.
  unfold peirce. unfold double_negation_elimination. unfold not.
  intros H1 P H2. apply H1 with (Q := False). intros H3. destruct H2. apply H3.
Qed.