Require Import Reals.

Fixpoint fibonacci (n : nat) : R :=
  match n with
  | O => 1
  | S n' => match n' with
            | O => 1
            | S n'' => fibonacci(n') + fibonacci(n'')
            end
  end.

Global Notation F := fibonacci.

Definition a (n : nat) : R :=
  match n with
  | 0 => 2
  | _ => F(2*n) / F(2*n-1)
  end.

Definition b (n : nat) : R := F(2*n + 1) / F(2*n).

Definition c (n : nat) : R := F(n + 1) / F n.

Definition b_minus_a (n : nat) : R := b n - a n.