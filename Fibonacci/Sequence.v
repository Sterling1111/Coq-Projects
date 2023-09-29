Require Export Reals.

Open Scope R_scope.

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

Definition b (n : nat) : R := F(2*n+1) / F(2*n).

Definition c (n : nat) : R := F(n+1) / F n.

Definition b_minus_a (n : nat) : R := b n - a n.

Definition sequence := nat -> R.

Definition decreasing (a : sequence) : Prop :=
  forall n : nat, a n >= a (S n).

Definition increasing (a : sequence) : Prop :=
  forall n : nat, a n <= a (S n).

(* Stating that a sequence is bounded below *)
Definition bounded_below (a : sequence) : Prop :=
  exists LB : R, forall n : nat, LB <= a n.

Definition bounded_above (a : sequence) : Prop := 
  exists UB : R, forall n : nat, UB >= a n.

Definition convergent_sequence (a : sequence) : Prop :=
  exists (L : R), 
    forall (eps : R), eps > 0 ->
      exists (N : nat), forall (n : nat), (n >= N)%nat -> Rabs (a n - L) < eps.

Definition limit_of_sequence (a : nat -> R) (L : R) : Prop :=
  forall eps : R, eps > 0 ->
                  exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (a n - L) < eps.

Definition arbitrarily_small (a : sequence) : Prop :=
  limit_of_sequence a 0.

Definition monotonic_sequence (a : sequence) : Prop :=
  (increasing a /\ bounded_above a) \/ (decreasing a /\ bounded_below a).

Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x >= m.

Definition has_lower_bound (E:R -> Prop) := exists m : R, is_lower_bound E m.

Definition is_glb (E:R -> Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> m >= b).

Definition one_over_n (n : nat) : R := 1 / INR n.