

(* just do std lib Power_Set dont use this*)
Definition Power_Set {U : Type} (A : Ensemble U) : Ensemble (Ensemble U) :=
  fun B => B ⊆ A.

Definition Finite_Set {U : Type} (A : Ensemble U) : Prop :=
  exists n : ℕ, exists l : list U, FromList l = A.

Proposition prop_14_6 : forall (U : Type) (A : Ensemble U) (n : ℕ),
  Finite_Set A -> cardinal U A n -> cardinal (Ensemble U) (Power_Set A) (2^n).
Proof.
  intros U A n [m [l H1]] H2. 
Admitted.