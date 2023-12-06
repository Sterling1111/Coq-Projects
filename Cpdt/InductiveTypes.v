Require Import List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Check (fun x : nat => x).
Check (fun x : True => x).
Check I.
Check (fun _ : False => I).
Check (fun x : False => x).

Inductive unit : Set := 
| tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
  destruct x. reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Check Empty_set_ind.

Definition e2u (e : Empty_set) : unit := match e with end.

Inductive bool : Set :=
  | true
  | false.

Definition negb (b : bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition negb' (b : bool) : bool := 
  if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq : forall (b : bool),
  negb b <> b.
Proof.
  destruct b; discriminate.
Qed.

Check bool_ind.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Definition isZero (n : nat) : bool := 
  match n with
  | O => true
  | _ => false
  end.

Definition pred (n : nat) : nat := 
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
Proof.
  intro; reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
Proof.
  induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Restart.
  induction n; crush.
Qed.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1; trivial.
Qed.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp : forall l1 l2 : nat_list, 
  nlength (napp l1 l2) = plus (nlength l1) (nlength l2).
Proof.
  induction l1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
  induction n1; crush.
Qed.

#[local] Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
  = plus (nsize tr2) (nsize tr1).
  induction tr1; crush.
Qed.

Check nat_btree_ind.

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil => O
  | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app : forall T (ls1 ls2 : list T), length (app ls1 ls2)
  = plus (length ls1) (length ls2).
  induction ls1; crush.
Qed.

Reset list.

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2)
    = plus (length ls1) (length ls2).
    induction ls1; crush.
  Qed.
End list.

Arguments Nil {T}.

Print list.
Check length.
Check list_ind.

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
  induction el1; crush.
Abort.

Check even_list_ind.

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply nat_ind.
  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).

  apply (even_list_mut
    (fun el1 : even_list => forall el2 : even_list,
      elength (eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol : odd_list => forall el : even_list,
      olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjuction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conjuction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
  | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
  induction f; crush.
Qed.

Check formula_ind.

Print nat_ind.

Check nat_rect.

Print nat_rec.

Fixpoint plus_recursive (n : nat) : (nat -> nat) :=
  match n with
  | O => fun m => m
  | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat := 
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).

Compute (plus_rec (S (S (S O))) (S (O))).

Theorem plus_equivalent : plus_recursive = plus_rec.
  reflexivity.
Qed.

Print nat_rect.

Fixpoint nat_rect' (P : nat -> Type) 
                   (HO : P O)
                   (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
  | O => HO
  | S n' => HS n' (nat_rect' P HO HS n')
  end.

Section nat_ind'.

  Variable P : nat -> Prop.

  Hypothesis O_case : P O.

  Hypothesis S_case : forall n : nat, P n -> P (S n).

  Fixpoint nat_ind' (n : nat) : P n :=
    match n with
    | O => O_case
    | S n' => S_case (nat_ind' n')
    end.
End nat_ind'.

Print even_list_mut.