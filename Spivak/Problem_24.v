Require Import Reals List.
Import ListNotations.

Open Scope R_scope.

Fixpoint standard_sum (l : list R) : R := 
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => x + standard_sum xs
  end.

Example ex_3 : forall a b c,
  standard_sum [a;b;c] = a + (b + c).
Proof.
  intros a b c. simpl. reflexivity.
Qed.

Example ex_4 : forall a b c d,
  standard_sum [a;b;c;d] = a + (b + (c + d)).
Proof.
  intros a b c d. simpl. reflexivity.
Qed.

Lemma lemma_1_24_a : forall l a,
  a + standard_sum l = standard_sum (a :: l).
Proof.
  intros l a. destruct l as [| a' l'] eqn : El.
  - simpl. apply Rplus_0_r.
  - simpl. reflexivity.
Qed.

Lemma lemma_1_24_b : forall l1 l2,
  standard_sum l1 + standard_sum l2 = standard_sum (l1 ++ l2).
Proof.
  intros l1 l2. induction l1 as [| a' l1' IH].
  - simpl. apply Rplus_0_l.
  - replace ((a' :: l1') ++ l2) with (a' :: (l1' ++ l2)).
    2 : { simpl. reflexivity. }
    repeat rewrite <- lemma_1_24_a. rewrite <- IH. apply Rplus_assoc.
Qed.

Inductive add_expr : Type := 
| Num (a : R) 
| Sum (e1 e2 : add_expr).

(* a -> a*)
(* a b -> a + b*)
(* a b c -> a + (b + c), (a + b) + c*)

Section LocalScope.
  Variable a b c : R.

  Check (Num a).
  Check (Sum (Num a) (Num b)).
  Check (Sum (Num a) (Sum (Num b) (Num c))).
  Check (Sum (Sum (Num a) (Num b)) (Num c)).

End LocalScope.

(* a | b c d -> a + (b + (c + d)), a + ((b + c) + d)*)
(* a b | c d -> (a + b) + (c + d)*)
(* a b c | d -> (a + (b + c)) + d, ((a + b) + c) + d*)

Fixpoint eval_add_expr (e : add_expr) : R := 
  match e with
  | Num a => a
  | Sum e1 e2 => eval_add_expr e1 + eval_add_expr e2
  end.

Fixpoint elements (e : add_expr) : list R := 
  match e with
  | Num a => [a]
  | Sum e1 e2 => elements e1 ++ elements e2
  end.

Lemma lemma_1_24_c : forall e : add_expr,
  eval_add_expr e = standard_sum (elements e).
Proof.
  intros e. induction e as [a | e1 IH1 e2 IH2].
  - simpl. reflexivity.
  - simpl. rewrite <- lemma_1_24_b. rewrite IH1. rewrite IH2.
    reflexivity.
Qed.

Lemma Rplus_assoc_general : forall e1 e2,
  elements e1 = elements e2 -> eval_add_expr e1 = eval_add_expr e2.
Proof.
  intros e1 e2 H. repeat rewrite lemma_1_24_c. rewrite H. reflexivity.
Qed.