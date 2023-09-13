From Foundations Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat))) : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. simpl. reflexivity. Qed.

Example test_repeat2 : repeat bool false 1 = cons bool false (nil bool).
Proof. simpl. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(*
d (b a 5)         NO d must be followed by a type
d mumble (b a 5)  YES
d bool (b a 5)    YES
e bool true       YES
e mumble (b c 0)  YES
e bool (b c 0)    NO e must take type bool not mumble
c                 NO c is of type mumble
*)
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S n => cons X x (repeat' X x n)
  end.

Check repeat' : forall X : Type, X -> nat -> list X.

Check repeat : forall X : Type, X -> nat -> list X.

 Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S n => cons _ x (repeat'' _ x n)
  end.

Definition list123 := 
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := 
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := 
  cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S n => cons x (repeat''' x n)
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons _ t => S (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl. reflexivity. Qed.

Example test_rev2 :
  rev (cons true nil) = cons true nil.
Proof. simpl. reflexivity. Qed.

Example test_length1 : length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. simpl. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X : Type), forall l : list X, 
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| n l' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem app_assoc : forall X (l1 l2 l3 : list X),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros X l1 l2 l3.
  induction l1 as [| n l1' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length(l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| n l1' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity. 
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| n l1' IH].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IH. rewrite -> app_assoc. reflexivity.  
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| n l' IH].
  simpl. reflexivity.
  simpl. rewrite -> rev_app_distr. rewrite -> IH. simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X := 
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y := 
  match p with
  | (x , y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx , y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

Module OptionPlayground.

Inductive option (X:Type) : Type :=
 | Some (x : X)
 | None.

Arguments Some {X}.
Arguments None{X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | h :: t => match n with
              | O => Some h
              | S n' => nth_error t n'
              end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof. simpl. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X := 
  f ( f ( f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times : doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times' : doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1 : filter even [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool := 
  (length l) =? 1.

Example test_filter2:
  filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed. 
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2' : 
  filter (fun l => (length l) =? 1)
          [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (even n) (negb (n <=? 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed. 
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  ((filter test l), (filter (fun n => negb (test n)) l)).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed. 
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity. Qed.

Example test_map2 : map odd [2;1;2;5] = [false;true;false;true].
Proof. simpl. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. simpl. reflexivity. Qed.

Lemma map_plus_1 : forall (X Y : Type) (f : X -> Y) (l : list X) (n : X),
  map f (l ++ [n]) = map f l ++ [f n].
Proof.
  intros X Y f l n.
  induction l as [| k l' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity. 
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| n l' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. rewrite -> map_plus_1. reflexivity. 
Qed.

Fixpoint flat_map {X Y : Type} (f: X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. simpl. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(*
Fixpoint filter (X : Type) (test : X -> bool) (l : list X) : list X :=
  match l with
  | nil _ => nil X
  | cons _ h t => if test h then cons X h (filter' X test t)
                  else filter' X test t
  end.  
  
Fixpoint map (X Y : Type) (f : X -> Y) (l : list X) : list Y:=
  match l with
  | nil _ => nil Y
  | cons _ h t => cons Y (f h) (map X Y f t)
  end.
*)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. simpl. reflexivity. Qed.
  
Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. simpl. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. simpl. reflexivity. Qed. 

Definition constfun {X : Type} (x : X) : nat -> X := 
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.

Check plus3 : nat -> nat.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat := 
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| n l' IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun h t => f h :: t) l [].

Example fold_map_test : fold_map minustwo [5;4;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.   
  
Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [| n l' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. reflexivity. 
Qed.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z := 
  f (fst p) (snd p).

Example test_map1' : map (plus 3) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y, 
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : X * Y -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.

Theorem nth_error_bound : forall (X : Type) (l : list X) (n : nat),
  length l = n -> nth_error l n = None.
Proof.
  intros X l.
  induction l as [| h l' IH].
  - intros n H. simpl. reflexivity.
  - intros n H. destruct n as [| n'] eqn:En.
    * simpl. discriminate.
    * simpl. apply IH. simpl in H. injection H as H2. apply H2. 
Qed.

Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.
Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat := @doit3times.

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.
Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.

Definition scc (n : cnat) : cnat := 
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(*m X f is a function that takes an x and applies f m times*)
(*n X (m X f) x applies (m X f) to x n times since each application of
  m X f applies f to x m times we have m * n*)

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(*n X is a function that takes *)

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed. 
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.

End Exercises.