Require Export Reals.

Open Scope R_scope.

Definition sequence := nat -> R.

Definition decreasing (a : sequence) : Prop :=
  forall n : nat, a n >= a (S n).

Definition increasing (a : sequence) : Prop :=
  forall n : nat, a n <= a (S n).

Definition eventually_decreasing (a : sequence) : Prop :=
  exists (N : nat),
    forall (n : nat), (n >= N)%nat -> a n >= a (S n).

Definition eventually_increasing (a : sequence) : Prop :=
  exists (N : nat),
    forall (n : nat), (n >= N)%nat -> a n <= a (S n).

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