Require Import List.
Import ListNotations.

Inductive Expr : Type :=
| Num (n : nat)
| Op (e1 e2 : Expr).

Compute (Op (Num 1) (Num 2)).

Fixpoint eval (e : Expr) (op : nat -> nat -> nat) : nat :=
  match e with
  | Num n => n
  | Op e1 e2 => op (eval e1 op) (eval e2 op)
  end.

Definition e1 : Expr := Op (Num 1) (Num 2).

Compute (eval e1 mult).

Compute flat_map (fun n => n + 2) (seq 1 5).

Fixpoint parenthesize (lst : list nat) : list Expr :=
  match lst with
  | [] => []
  | x :: xs => match xs with
                | [] => [Num x]
                | _ :: _ =>
                    flat_map
                      (fun split_point : nat =>
                      let left := firstn split_point lst in
                      let right := skipn split_point lst in
                      flat_map (fun l : Expr => map (fun r : Expr => Op l r) (parenthesize right)) (parenthesize left))
                      (seq 1 (Nat.pred (length lst)))
                end
  end.