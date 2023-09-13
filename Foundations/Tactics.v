From Foundations Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m -> n = m.
Proof.
  intros.
  apply H.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros.
  apply H0. apply H.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros.
  apply H0. apply H. apply H1.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros.
  Search rev.
  rewrite -> H.
  symmetry. apply rev_involutive.
Qed.

(*apply use implications to transform gaosl and hypotheses, rewrite replaces a term with an
  equivalent term if the equivalence of the terms has already been proven*)

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
intros a b c d e f eq1 eq2.
rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. 
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. 
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) -> 
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m. apply H0. apply H.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros.
  injection H as Hmn. apply Hmn. 
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  n :: m :: nil = o :: o :: nil ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  assert (x :: y :: l = z :: z :: l). {rewrite -> H. rewrite -> H0. reflexivity. }
  injection H1 as H2 H3.
  rewrite -> H2. rewrite -> H3. reflexivity.
Qed.

Theorem discriminate_ex : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros.
  discriminate H.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros.
  discriminate H.
Qed.

Example discriminate_ex3 : forall (X : Type) (x y z : X) (l h : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem eqb_0_l : forall n,
  0 =? n = true -> n = 0.
Proof.
  intro n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl. intros H. discriminate. 
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros.
  rewrite -> H. reflexivity.
Qed.


Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros.
  apply f_equal. apply H.
Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros.
  f_equal. apply H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros.
  simpl in H. apply H.
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros. symmetry in H0. apply H in H0. symmetry in H0.
  apply H0.
Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  induction n as [| n' IH].
  - simpl. intros H. destruct m as [| m'] eqn:E.
    * reflexivity.
    * simpl in H. discriminate H.
  - intros H. destruct m as [| m'] eqn:E.
    * simpl in H. discriminate H.
    * f_equal. 
Abort.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| k IH].
  - intros m H. simpl in H. destruct m as [| m'] eqn:Em.
    * reflexivity.
    * discriminate.
  - intros m H. destruct m as [| m'] eqn:Em.
    * discriminate.
    * f_equal. apply IH. simpl in H. injection H as H2. apply H2. 
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intro n.
  induction n as [| k IH].
  - intros m H. destruct m as [| m'] eqn:Em.
    * reflexivity.
    * discriminate H.
  - intros m H. destruct m as [| m'] eqn:Em.
    * discriminate H.
    * f_equal. apply IH. simpl in H. apply H.
Qed.

(*
Theorem : for all nat n m, n =? m = true -> n = m.
  Let k : nat. Show that for all m : nat k =? m = true -> k = m.
    Show that P(k = 0) is true: 
      Case m = 0:
        0 = 0 follows by reflexivity.
      Case m = S m': 
        (0 =? S m' = true) -> false = true so the conclusion follows vacuously.

    IH : for all m : nat, k =? m = true -> k = m.

    Show that P(k = S k) is true:
      Case m = 0:
        (S k =? 0 = true) -> false = true so the conclusion follows vacuously.
      Case m = Sm':
        Goal is to show that S k = S m'. Since S k = S m' iff k = m' it will 
        suffice to show that k = m' which is now our goal. Now consider our IH 
        which takes the form a -> b. We want to show b so if we show a then b
        will follow by IH. So now our goal is a which is (k =? m') = true. Now
        we can simply our hypothesis which is that (S k =? S m') = true to 
        (k =? m') = true by definition of =?. This hypothesis is our goal and so
        the goal is true. 
Qed.
*)

Theorem plus_n_n_injection : forall n m,
  n + n = m + m -> n = m.
Proof.
  intro n.
  destruct n as [| n'] eqn:En.
  - intros m H. simpl in H. destruct m as [| m'] eqn:Em.
    * reflexivity.
    * simpl in H. discriminate H.
  - intros m H. rewrite <- double_plus in H. rewrite <- double_plus in H. 
    apply double_injective. apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* We are stuck here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h l' IH].
  - simpl. reflexivity.
  - intros n H. destruct n as [| n'] eqn:En.
    * simpl in H. discriminate H.
    * simpl. apply IH. simpl in H. injection H as H2. apply H2.
Qed.

Definition square (n : nat) := n * n.

Lemma square_mul : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros.
  unfold square.
  rewrite -> mult_assoc.
  assert (H: n * m * n = n * n * m).
    {rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_1 : forall m,
  foo m + 1 = foo (m + 1) + 1.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Definition bar x := 
  match x with
  | O => 5
  | S _ => 5
  end.
  
Fact silly_fact_2_FAILED : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intro.
  simpl.
Abort.

Fact silly_fact_2 : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intro.
  destruct m as [| m'] eqn:Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intro.
  unfold bar.
  destruct m as [| m'] eqn:Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool := 
  if n =? 3 then false
  else if n =? 5 then false
  else false.

  Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. 
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
                : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

  
Theorem combine_split : forall X Y (l : list (X * Y)) (l1 : list X) (l2 : list Y),
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IH].
  - intros. simpl in H. injection H as H2 H3. 
    rewrite <- H2. rewrite <- H3. simpl. reflexivity.
  - intros. destruct h as [x y]. simpl in H. destruct (split t). injection H as H2 H3.
    rewrite <- H2. rewrite <- H3. simpl. f_equal. rewrite IH. reflexivity. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - (*n =? 3 = true*) apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (*n =? 3 = false*) destruct (n =? 5) eqn:Heqe5.
    * (*n =?5 = true*) apply eqb_true in Heqe5. rewrite -> Heqe5. reflexivity.
    * (*n =?5 = false*) discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct (b) eqn:E1.
  - (*b = true*) destruct (f true) eqn:E2.
    * (*f true = true*) rewrite -> E2. rewrite -> E2. reflexivity.
    * (*f true = false*) destruct (f false) eqn:E3.
      + (*f false = true*) rewrite -> E2. reflexivity.
      + (*f false = false*) rewrite -> E3. reflexivity.
  - (*b = false*) destruct (f false) eqn:E2.
    * (*f false = true*) destruct (f true) eqn:E3.
      + (*f true = true*) rewrite -> E3. reflexivity.
      + (*f true = false*) rewrite -> E2. reflexivity.
    * (*f false = false*) rewrite -> E2. rewrite -> E2. reflexivity.
Qed.

Theorem eqb_sym : forall n m : nat,
  (n =? m) = (m =? n).
Proof.
  intro n.
  induction n as [| k IH].
  - intro m. destruct m as [| m'].
    * simpl. reflexivity.
    * simpl. reflexivity.
  - intro m. destruct m as [| m'].
    * simpl. reflexivity.
    * simpl. apply IH.
Qed.

Lemma eqb_true_converse : forall n m : nat,
  n = m -> n =? m = true.
Proof.
  intros. generalize dependent m.
  induction n as [| k IH].
  - intros. rewrite <- H. simpl. reflexivity.
  - intros. destruct m as [| m'].
    * discriminate H.
    * simpl. injection H as H1. apply IH. apply H1. 
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros.
  apply eqb_true in H.
  rewrite <- H in H0. apply H0.
Qed.

Definition split_combine_statement : Prop := 
  forall X Y (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y.
  induction l1 as [| h t IH].
  - intros. simpl. f_equal. simpl in H. destruct l2. 
    * reflexivity.
    * simpl in H. discriminate H.
  - intros. simpl. destruct l2. 
    * simpl in H. discriminate H.
    * simpl. simpl in H. injection H as H'. rewrite -> IH.
      reflexivity. apply H'.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros.
  induction l as [| h t IH].
  - intros. simpl in H. discriminate H.
  - intros. simpl in H. destruct (test h) eqn:E.
    * injection H as H2 H3. rewrite <- H2. apply E.
    * apply IH. apply H.
Qed.  

Fixpoint forallb {X : Type} (f : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: t => match f h with
              | true => forallb f t 
              | false => false
              end
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
  
Fixpoint existsb {X : Type} (f : X -> bool) (l : list X) : bool :=
  match l with
  | nil => false
  | h :: t => match f h with
              | true => true
              | false => existsb f t
              end
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (f : X -> bool) (l : list X) : bool := 
  negb (forallb (fun x => negb (f x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test.
  induction l as [| h t IH].
  - reflexivity.
  - unfold existsb'. simpl. destruct (test h) eqn:E1.
    * (*test h = true*) simpl. reflexivity.
    * (*test h = false*) simpl. rewrite -> IH. reflexivity.
Qed.