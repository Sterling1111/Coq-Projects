Require Import List.
Import ListNotations.

Require Import Coq.Program.Wf.
Require Import Lia.
Require Import Coq.Arith.Arith.

Definition Associative {A : Type} (op : A -> A -> A) : Prop :=
  forall x y z : A, op x (op y z) = op (op x y) z.

Inductive expr : Type :=
| Num (n : nat)
| Op (e1 e2 : expr).

Compute (Op (Num 1) (Num 2)).

Fixpoint eval (op : nat -> nat -> nat) (e : expr) : nat :=
  match e with
  | Num n => n
  | Op e1 e2 => op (eval op e1) (eval op e2)
  end.

Fixpoint elements (e : expr) : list nat :=
  match e with
  | Num n => [n]
  | Op e1 e2 => elements e1 ++ elements e2
  end.

Definition e1 : expr := Op (Num 1) (Num 2).

Compute (eval mult e1).

Check (eval mult).

Compute flat_map (fun n => map (fun m => m + n) ([1; 2; 3])) (seq 7 3).

(* Define a well-founded relation based on the length of the list. *)
Definition lengthOrder (l1 l2 : list nat) := length l1 < length l2.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder. intros. induction ls.
    - apply Acc_intro. intros. inversion H0.
    - apply Acc_intro. intros. apply Acc_intro. intros. apply IHls.
      -- simpl in H. lia.
      -- assert (length y0 < length (a :: ls)) by lia. 
         assert (length (a :: ls) = length ls + 1).
         --- simpl. lia.
         --- lia.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red. intro. eapply lengthOrder_wf'. eauto.
  Defined.
  
Lemma firstn_lengthOrder : forall (l : list nat) (n : nat),
  n < length l -> lengthOrder (firstn n l) l.
Proof.
  intros l n. unfold lengthOrder. rewrite firstn_length. lia.
Defined.

Lemma skipn_lengthOrder : forall (l : list nat) (n : nat),
  0 < n < length l -> lengthOrder (skipn n l) l.
Proof.
  intros l n. unfold lengthOrder. rewrite skipn_length. lia.
Defined.

Definition in_range (split_point len: nat) : {1 <= split_point <= Nat.pred len} + {split_point < 1 \/ Nat.pred len < split_point}.
Proof.
  destruct (le_lt_dec 1 split_point).
  - destruct (le_lt_dec split_point (Nat.pred len)).
    + left. lia.
    + right. lia.
  - right. lia.
Defined.

Definition parenthesize : list nat -> list expr.
refine (Fix lengthOrder_wf (fun _ => list expr)
  (fun (l : list nat)
    (parenthesize : forall l' : list nat, lengthOrder l' l -> list expr) =>
      match l with
      | [] => []
      | [x] => [Num x]  
      | x :: xs => 
        if le_lt_dec 2 (length l)
        then     
          flat_map
            (fun split_point : nat =>
              if in_range split_point (length l) then
                let left := firstn split_point l in
                let right := skipn split_point l in
                flat_map (fun el : expr => map (fun er : expr => Op el er) (parenthesize right _)) (parenthesize left _)
              else []
            )
            (seq 1 (Nat.pred (length l)))
        else []
      end)).
  - apply skipn_lengthOrder. lia.
  - apply firstn_lengthOrder. lia.
Defined.

Compute (last (parenthesize [1;2;3;4])).

Compute (map (eval plus) (parenthesize [1;2;3;4;5;6;7;8])).

Lemma lem2 : forall (l1 l2 : list nat) (op : nat -> nat -> nat), 
  Associative op ->
  fold_right op 0 (l1 ++ l2) = fold_right op 0 l1 + fold_right op 0 l2.
Proof.
  intros l1 l2. induction l1.
  - intros op H. simpl. reflexivity.
  - intros op H. simpl. rewrite IHl1.
Qed.

Check expr_ind.

Lemma lem3 : forall (e : expr),
  eval e = fold_right plus 0 (elements e).
Proof.
  intros e. induction e as [| e1 IH1 e2 IH2].
  - simpl. lia.
  - simpl. rewrite IH1. rewrite IH2. rewrite lem2. reflexivity.
Qed.

Theorem add_assoc_n : forall (e1 e2 : meaningful_expression),
  elements e1 = elements e2 -> meaningful_sum e1 = meaningful_sum e2.
Proof.
  intros e1 e2 H.
  repeat rewrite lem3. rewrite H. reflexivity.
Qed.