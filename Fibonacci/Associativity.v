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

Compute flat_map (fun n => map (fun m => m + n) ([1; 2; 3])) (seq 7 3).

Fixpoint parenthesize (l : list nat) : list Expr :=
  match l with
  | [] => []
  | x :: xs => match xs with
                | [] => [Num x]
                | _ :: _ =>
                    flat_map
                      (fun split_point : nat =>
                      let left := firstn split_point l in
                      let right := skipn split_point l in
                      flat_map (fun el : Expr => map (fun er : Expr => Op el er) (parenthesize right)) (parenthesize left))
                      (seq 1 (Nat.pred (length l)))
                end
  end.