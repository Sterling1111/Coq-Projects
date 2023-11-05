Set Warnings "-notation-overridden,-parsing,-deprecated-hint-withoutlocality".
From Foundations Require Export Logic.
From Coq Require Import Lia.

Fixpoint div2 (n : nat) :=
  match n with 
  | O => O
  | 1 => O
  | S (S n') => S (div2 n')
  end.

Definition f (n : nat) := 
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Module LePlayground.
  
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) : R x y -> clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive clos_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) : R x y -> clos_refl_trans R x y
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z
  | rt_refl (x : X) : clos_refl_trans R x x.

Inductive clos_sym_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | srt_step (x y : X) : R x y -> clos_sym_refl_trans R x y
  | srt_trans (x y z : X) :
      clos_sym_refl_trans R x y ->
      clos_sym_refl_trans R y z ->
      clos_sym_refl_trans R x z
  | srt_refl (x : X) : clos_sym_refl_trans R x x
  | srt_sym (x y : X) : 
      clos_sym_refl_trans R x y ->
      clos_sym_refl_trans R y x.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) : ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  repeat apply ev_SS. apply ev_0.  
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros. simpl. repeat apply ev_SS. apply H.
Qed.

Theorem ev_double : forall n : nat,
  ev (double n).
Proof.
  intros. induction n as [| k IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_inversion : forall n : nat,
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n H. destruct H as [| n''] eqn:En'.
  - left. reflexivity.
  - right. exists n''. split.
    -- reflexivity.
    -- apply e.
Qed.

