Inductive bool : Type := 
| true
| false.

Definition negb (b:bool) : bool:= 
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1:bool) (b2:bool) : bool := 
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Definition negb' (b:bool) : bool :=
    if b then false
    else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
    if b1 then b2
    else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
    if b1 then true
    else b2.
    
Definition nandb  (b1:bool) (b2:bool) : bool :=
    match b1 with
    | false => true
    | true => (negb b2)
    end.
    
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
    
Example test_orb1: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Definition xorb (a b : bool) : bool := 
  match a with
  | false => b
  | true => negb b
  end.

Example xorb_test1: xorb true true = false.
Proof. reflexivity. Qed.
Example xorb_test2: xorb true false = true.
Proof. reflexivity. Qed.
Example xorb_test3: xorb false true = true.
Proof. reflexivity. Qed.
Example xorb_test4: xorb false true = true.
Proof. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "x ^ y" := (xorb x y).

Example test_orb5: true && false = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    match b1 with
    | false => false
    | true => (andb b2 b3) 
    end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed. 
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

Theorem negb_negb : forall (b:bool), negb (negb b) = b.
Proof.
    intros b.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Compute (next_weekday (next_weekday friday)).
Compute (next_weekday friday).

Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.

Proof.
    simpl.
    reflexivity.
Qed.

Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive color : Type := 
    | black
    | white
    | primary (p : rgb).

Definition monochrome (c:color) : bool := 
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

Definition isred (c:color) : bool :=
    match c with
    | black => true
    | white => true
    | primary red => true
    | primary _ => false
    end.

Module Playground.
    Definition b : rgb := blue.
End Playground.
    
Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
    Inductive bit : Type :=
        | B0
        | B1.

    Inductive nybble : Type :=
        | bits (b0 b1 b2 b3 : bit).

    Check (bits B1 B0 B1 B0) : nybble.

    Definition all_zero (nb:nybble) : bool :=
        match nb with
        | (bits B0 B0 B0 B0) => true
        | (bits _ _ _ _) => false
        end.

    Compute (all_zero (bits B1 B1 B0 B0)).
    Compute (all_zero (bits B0 B0 B0 B0)).
    
End TuplePlayground.

Module Type NatPlayground.
    Inductive nat : Type :=
        | O
        | S (n : nat).

    Definition pred (n:nat) : nat := 
        match n with
        | O => O
        | S n' => n'
        end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n:nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Compute (minustwo 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Definition odd (n:nat) : bool :=
    negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
    Fixpoint plus (n:nat) (m:nat) : nat := 
        match n with
        | O => m
        | S n' => S (plus n' m)
        end.

    Compute plus 3 2.

    Fixpoint mult (n m : nat) : nat :=
        match n with
        | O => O
        | S n' => plus m (mult n' m)
        end.
    
    Example test_mult1: (mult 3 3) = 9.
    Proof. simpl. reflexivity. Qed.    

    Fixpoint minus (n m:nat) : nat :=
        match n, m with
        | O, _ => O
        | S _, O => n
        | S n', S m' => minus n' m'
        end.

    Example test_minus: (minus 3 3) = 0.
    Proof. simpl. reflexivity. Qed.         
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

Example exp_test: exp 2 3 = 8.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S n' => mult n (factorial n')
    end.

Example fact_test1: factorial 3 = 6.
Proof. simpl. reflexivity. Qed.
Example fact_test2: factorial 5 = mult 10 12.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m:nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
           | O => false
           | S m' => eqb n' m'
           end
    end.

Fixpoint eqb' (n m:nat) : bool :=
    match n, m with
    | S n', S m' => eqb' n' m'
    | O, O => true
    | _, _ => false
    end.

Example eqb_test: eqb 3 3 = true.
Proof. simpl. reflexivity. Qed.

Example eqb'_test: eqb' 6 19 = false.
Proof. simpl. reflexivity. Qed.

Example eqb'_test2: eqb 3 3 = true.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m:nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => leb n' m'
              end   
    end.
    
Example leb_test: leb 3 2 = false.
Proof. simpl. reflexivity. Qed.

Example leb_test2: leb 2 3 = true.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3: 3 <=? 3 = true.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m:nat) : bool :=
    match n, m with
    | S n', S m' => leb (S n') m'
    | _, O => false
    | O, _ => true
    end. 

    Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
    Example test_ltb1: (ltb 2 2) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_ltb2: (ltb 2 4) = true.
    Proof. simpl. reflexivity. Qed. 
    Example test_ltb3: (ltb 4 2) = false.
    Proof. simpl. reflexivity. Qed.

    Theorem plus_O_n : forall n : nat, 0 + n = n.
    Proof. intros n. simpl. reflexivity. Qed.

    Theorem plus_O_n': forall n : nat, 0 + n = n.
    Proof.
        intros n. simpl. reflexivity.
    Qed.

    Theorem plus_1_1 : forall n : nat, 1 + n = S n.
    Proof.
        intros n. reflexivity.
    Qed.

    Theorem mult_0_1: forall n : nat, 0 * n = 0.
    Proof.
        intros n. reflexivity.
    Qed.

Theorem plus_id_example: forall n m:nat, n = m -> n + n = m + m.
Proof.
    (*move both quantifiers into the context: *)
    intros n m.
    (*move the hypothesis into the context: *)
    intros hypothesis.
    (*rewrite the goal using the hypothesis: *)
    rewrite -> hypothesis.
    reflexivity.
Qed.

Theorem plus_id_example': forall n m:nat, n = m -> n + n = m + m.
Proof.
    intros n m.
    intros hypothesis.
    rewrite <- hypothesis.
    reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros hypothesis1.
    rewrite -> hypothesis1.
    intros hypothesis2.
    rewrite hypothesis2.
    reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.


Theorem mult_n_1: forall p : nat, p * 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat, (n + 1) =? 0 = false.
Proof.
    intros n.
    simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat, (n + 1) =? 0 = false.
Proof.
    intros n. destruct n as [| n'] eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b.
    destruct b eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_commutative : forall b c : bool, andb b c = andb c b.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
     + reflexivity.
     + reflexivity.
    - destruct c eqn:Ec.
     + reflexivity.
     + reflexivity.
Qed.

Theorem nadb3_exchange : forall a b c : bool, andb (andb a b) c = andb (andb a c) b.
Proof.
 intros a b c.
 destruct a eqn:Ea.
  * destruct b eqn:Eb.
   ** destruct c eqn:Ec.
    - reflexivity.
    - reflexivity.
   ** destruct c eqn:Ec.
    - reflexivity.
    - reflexivity.
  * destruct b eqn:Eb.
   ** destruct c eqn:Ec.
    - reflexivity.
    - reflexivity.
   ** destruct c eqn:Ec.
    - reflexivity.
    - reflexivity.            
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
    * destruct c eqn:Ec.
      { simpl. intros hypothesis. assumption. }
      { simpl. intros hypothesis. assumption. }
    * destruct c eqn:Ec.
      { simpl. intros hypothesis. reflexivity. }
      { simpl. intros hypothesis. assumption. }
Qed.

Theorem plus_1_neq_0' : forall n : nat, (n + 1) =? 0 = false.
Proof.
  intros [|n].
  reflexivity.
  reflexivity.
Qed.

Theorem andb_commutative'' : forall a b : bool, andb a b = andb b a.
Proof.
  intros [][].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, 0 =? (n + 1) = false.
Proof.
  intros [|n].
  reflexivity.
  reflexivity. 
Qed.

(*Fixpoint func (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => func O
  end.*)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool) , f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f hypothesis [].
  - rewrite -> hypothesis.
    rewrite -> hypothesis.
    reflexivity.
  - rewrite -> hypothesis.
    rewrite -> hypothesis.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f hypothesis [].
  - rewrite -> hypothesis.
    rewrite -> hypothesis.
    reflexivity.
  - rewrite -> hypothesis.
    rewrite -> hypothesis.
    reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros [][].
  - simpl. intros hypothesis. assumption.
  - simpl. intros hypothesis. rewrite -> hypothesis. reflexivity.
  - simpl. intros hypothesis. assumption.
  - simpl. intros hypothesis. assumption.
Qed.

Theorem xor_a_b_a_is_b : forall a b : bool, xorb (xorb a b) a = b.
Proof.
  intros [][].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. 
Qed.

Theorem xor_commutative : forall a b : bool, 
  xorb a b = xorb b a.
Proof.
  intros [][].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Check xor_a_b_a_is_b.

Compute true ^ false.

Compute true ^ false ^ true ^ true ^ false.
Check xor_a_b_a_is_b.
Check xor_commutative.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin := 
  match m with
  | Z => (B1 Z)
  | B0 m' => B1 m' 
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat := 
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 2 * (bin_to_nat m') + 1
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.  
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed. 

Check day.
Check tuesday.