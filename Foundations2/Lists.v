From Foundations2 Require Export Induction.

Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl.
Abort.
  
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intro p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros [n m]. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Compute mylist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := (nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil )..).

Fixpoint repeat (count n : nat) : natlist :=
  match count with
  | O => []
  | S count' => n :: (repeat count' n)
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => O
  | h :: t => 1 + (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.
Example test_app2 : [] ++ [1;2] = [1;2].
Proof. simpl. reflexivity. Qed.
Example test_app3 : [1;2] ++ [] = [1;2].
Proof. simpl. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat := 
  match l with
  | [] => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist := 
  match l with
  | [] => []
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => match h with
              | O => nonzeros t
              | _  => h :: (nonzeros t)
              end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

From Foundations2 Require Import Basics.

Check bin_to_nat.
Check andb'.

Compute (odd 3).

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => match (odd h) with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat := length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], [] => []
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => [h1;h2] ++ (alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => O
  | h ::t => match (eqb h v) with
              | true => 1 + (count v t)
              | false => count v t
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
  simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t => match (eqb h v) with
              | true => true
              | false => member v t
              end
  end.            
  
Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => match (eqb h v) with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.


Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => match (eqb h v) with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end 
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1, s2 with 
  | [], [] => true
  | [], _ => true
  | _, [] => false
  | h1 :: t1, h2 :: t2 => match (member h1 s2) with
                          | true => included t1 (remove_one h1 s2)
                          | false => false
                          end
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed. 
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem add_inc_count : forall (s : bag) (v : nat),
  length (add v s) = 1 + length s.
Proof.
  intros s v. destruct s as [| h t] eqn: Es.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intro l. destruct l as [| h t] eqn:El.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH.
   reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intro l. induction l as [| h' l' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. 
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity. 
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intro l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> app_length. simpl. rewrite -> IH. 
    rewrite -> add_comm. simpl. reflexivity.
Qed.

Search rev.
Search (_ + _ = _ + _).
Search (_ + _ = _ + _) inside Foundations2.Induction.

Search (?x + ?y = ?y + ?x).

Theorem app_nill_r : forall l : natlist,
l ++ [] = l.
Proof.
  intros l. induction l as [| k l'].
  - simpl. reflexivity.
  - simpl. rewrite-> IHl'. reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  rev(l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| h l' IH].
  - simpl. rewrite -> app_nill_r. reflexivity.
  - simpl. rewrite -> IH. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l. induction l as [| h l' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IH.
    reflexivity.
Qed.

Theorem app_assoc4 : forall (l1 l2 l3 l4 : natlist),
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1.
  - simpl. rewrite app_assoc. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| h l' IH].
  - simpl. reflexivity.
  - simpl. destruct h.
    -- rewrite IH. reflexivity.
    -- rewrite IH. simpl. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | h1 :: t1, h2 :: t2 => match (eqb h1 h2) with
                          | true => eqblist t1 t2
                          | false => false
                          end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Search (_ =? _).

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  induction l as [| h l' IH].
  - simpl. reflexivity.
  - simpl. destruct h as [| n'] eqn:Eh.
    -- simpl. apply IH.
    -- simpl. rewrite eqb_refl. apply IH.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intro l. simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n  <=? (S n) = true.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.

Theorem remove_does_not_increase_count : forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intro l. induction l as [| h l' IH].
  - simpl. reflexivity.
  - induction h as [| k IH2].
    --simpl. apply leb_n_Sn.
    -- simpl. apply IH.
Qed.




End NatList.
