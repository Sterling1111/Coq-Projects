Require Import List Lia Arith Classical.
Import ListNotations.

Fixpoint standard_sum (l : list nat) : nat := 
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => x + standard_sum xs
  end.

Lemma lemma_1_24_a : forall l a,
  a + standard_sum l = standard_sum (a :: l).
Proof.
  intros; destruct l; simpl; lia.
Qed.

Lemma lemma_1_24_b : forall l1 l2,
  standard_sum l1 + standard_sum l2 = standard_sum (l1 ++ l2).
Proof.
  intros l1 l2. induction l1 as [| a' l1' IH].
  - (simpl; lia).
  - replace ((a' :: l1') ++ l2) with (a' :: (l1' ++ l2)) by (simpl; reflexivity). 
    repeat rewrite <- lemma_1_24_a. lia.
Qed.

Inductive add_expr : Type := 
| Num (a : nat) 
| Sum (e1 e2 : add_expr).

Fixpoint eval_add_expr (e : add_expr) : nat := 
  match e with
  | Num a => a
  | Sum e1 e2 => eval_add_expr e1 + eval_add_expr e2
  end.

Fixpoint elements (e : add_expr) : list nat := 
  match e with
  | Num a => [a]
  | Sum e1 e2 => elements e1 ++ elements e2
  end.

Lemma lemma_1_24_c : forall e : add_expr,
  eval_add_expr e = standard_sum (elements e).
Proof.
  intros e. induction e as [a | e1 IH1 e2 IH2].
  - simpl. reflexivity.
  - simpl. rewrite <- lemma_1_24_b. lia.
Qed.

Lemma Nat_add_assoc_general : forall e1 e2,
  elements e1 = elements e2 -> eval_add_expr e1 = eval_add_expr e2.
Proof.
  intros e1 e2 H. repeat rewrite lemma_1_24_c. rewrite H. reflexivity.
Qed.

Ltac prove_equal :=
  let rec to_add_expr e :=
    match e with
    | ?a + ?b =>
      let a' := to_add_expr a in
      let b' := to_add_expr b in
      constr:(Sum a' b')
    | _ => constr:(Num e)
    end in
  match goal with
  | |- ?a = ?b =>
    let e1 := to_add_expr a in
    let e2 := to_add_expr b in
    change a with (eval_add_expr e1) in *;
    change b with (eval_add_expr e2) in *;
    assert (elements e1 = elements e2) by (compute; reflexivity);
    apply Nat_add_assoc_general; auto
  end.

Lemma dogs : forall a b c d e f g h i j k l m n o p q r s, 
  a + b + c + d + e + f + g + (h + (i + j + (k + l))) + (m + n + (o + p + (q + r) + s)) = 
  (a + b + (c + d)) + (e + (f + g + (h + i + j))) + k + l + m + n + o + p + q + r + s.
Proof.
  intros. prove_equal.
Qed.

Fixpoint remove_one {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                        (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if eq_dec x a then xs else x :: remove_one eq_dec a xs
  end.

Fixpoint reduce_freq_to_half {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                      (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => 
      let freq := count_occ eq_dec l x in
      repeat x (Nat.div2 freq) ++ remove eq_dec x (reduce_freq_to_half eq_dec xs)
  end.                        

Lemma remove_one_In : forall {A : Type} eq_dec (a : A) l,
  In a l -> count_occ eq_dec (remove_one eq_dec a l) a = pred (count_occ eq_dec l a).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct (eq_dec h a) as [H3 | H3]; try contradiction. reflexivity.
Qed.

Lemma remove_one_not_In : forall {A : Type} eq_dec (a : A) l,
  ~In a l -> remove_one eq_dec a l = l.
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + rewrite H2 in H1. rewrite not_in_cons in H1. tauto.
    + simpl. rewrite IH; auto. rewrite not_in_cons in H1. tauto.
Qed.

Lemma count_occ_remove_one_not_eq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma fold_right_In_gt_a : forall a l,
  In a l -> fold_right plus 0 l >= a.
Proof.
  intros a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + specialize (IH H1). lia.
Qed.

Lemma fold_right_remove_one_In : forall a l,
  In a l -> fold_right plus 0 (remove_one Nat.eq_dec a l) = fold_right plus 0 l - a.
Proof.
  intros a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (Nat.eq_dec h a) as [H3 | H3]; try nia.
    destruct H1 as [H1 | H1].
    + nia.
    + specialize (IH H1). simpl. rewrite IH. pose proof (fold_right_In_gt_a a t H1). nia.
Qed.

Lemma count_occ_eq_sum_right : forall l1 l2,
  (forall n, count_occ Nat.eq_dec l1 n = count_occ Nat.eq_dec l2 n) ->
  fold_right plus 0 l1 = fold_right plus 0 l2.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Nat.eq_dec l2 n = 0) by (intros n; specialize (H1 n); lia). 
    apply count_occ_inv_nil in H2. rewrite H2. reflexivity.
  - intros l2 H1. simpl. specialize (IH (remove_one Nat.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Nat.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
    }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Nat.eq_dec). lia. } rewrite fold_right_remove_one_In; auto. pose proof (fold_right_In_gt_a h l2 H3). lia.
Qed.

Lemma count_occ_eq_sum_right_prime : forall l1 l2,
  count_occ Nat.eq_dec l1 = count_occ Nat.eq_dec l2 -> fold_right plus 0 l1 = fold_right plus 0 l2.
Proof.
  intros l1 l2 H1. apply count_occ_eq_sum_right. intros n. rewrite H1. reflexivity.
Qed.

Lemma standard_sum_eq_sum_right : forall l1,
  standard_sum l1 = fold_right plus 0 l1.
Proof.
  intros l1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. destruct t.
    + simpl. lia.
    + simpl. lia. 
Qed.

Lemma nat_add_comm_general : forall e1 e2,
  (forall n, count_occ Nat.eq_dec (elements e1) n = count_occ Nat.eq_dec (elements e2) n) -> eval_add_expr e1 = eval_add_expr e2.
Proof.
  intros e1 e2 H1. apply count_occ_eq_sum_right in H1. repeat rewrite <- standard_sum_eq_sum_right in H1.
  repeat rewrite <- lemma_1_24_c in H1. auto.
Qed.

Fixpoint count_occ_all_eq (l1 l2 : list nat) : bool := 
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => if Nat.eq_dec h1 h2 then count_occ_all_eq t1 t2 else count_occ_all_eq t1 (remove_one Nat.eq_dec h1 l2)
  | _, _ => false
  end.

Compute (count_occ_all_eq [1; 2; 3] [2; 1; 3]).

Lemma count_occ_all_count_occ_eq : forall l1 l2,
  (forall n, count_occ Nat.eq_dec l1 n = count_occ Nat.eq_dec l2 n) -> count_occ_all_eq l1 l2 = true.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Nat.eq_dec l2 n = 0). { auto. } apply (count_occ_inv_nil Nat.eq_dec) in H2. rewrite H2. reflexivity.
  - intros l2 H1. destruct l2 as [| h2 t2].
    + simpl. rewrite count_occ_inv_nil in H1. inversion H1.
    + simpl. destruct (Nat.eq_dec h1 h2) as [H2 | H2].
      * apply IH. intros n. specialize (H1 n). rewrite H2 in H1. assert (n = h1 \/ n <> h1) as [H3 | H3] by apply classic.
        ++ rewrite count_occ_cons_eq in H1; try lia. simpl in H1. destruct (Nat.eq_dec h2 n); try lia.
        ++ rewrite count_occ_cons_neq in H1; try lia. rewrite H1. simpl. destruct (Nat.eq_dec h2 n); try lia.
      * destruct (Nat.eq_dec h2 h1) as [H3 | H3]; try nia. 

Lemma bullshit : forall a b c,
  (a + b) + c = c + (b + a).
Proof.
  intros a b c.
  set (e1 := Sum (Sum (Num a) (Num b)) (Num c)).
  set (e2 := Sum (Num c) (Sum (Num b) (Num a))).
  assert (H1 : count_occ Nat.eq_dec (elements e1) = count_occ Nat.eq_dec (elements e2)).
  { compute. reflexivity. }
Qed.