Require Import ZArith.
Require Import tree.

Open Scope positive_scope.

Section Radix.
  Context {A: Type}.

  Inductive tree : Type :=
  | Empty: tree
  | Node:  tree -> option A -> tree -> tree.

  Definition empty : tree := Empty.
  
  Fixpoint get (p: positive) (t: tree) : option A :=
    match p, t with
    | _,     Empty      => None
    | xH,    Node _ e _ => e
    | xO p', Node l _ _ => get p' l
    | xI p', Node _ _ r => get p' r
    end.

  Fixpoint set0 (p: positive) (e: A) : tree :=
    match p with
    | xH    => Node Empty (Some e) Empty
    | xO p' => Node (set0 p' e) None Empty
    | xI p' => Node Empty None (set0 p' e)
    end.

  Fixpoint set (p: positive) (e: A) (t: tree) : tree :=
    match p, t with
    | _,     Empty      => set0 p e
    | xH,    Node l _ r => Node l (Some e) r
    | xO p', Node l y r => Node (set p' e l) y r
    | xI p', Node l y r => Node l y (set p' e r)
    end.

  Theorem gempty:
    forall (i: positive), get i (empty) = None.
  Proof.
    intro i. case i; reflexivity.
  Qed.

  Theorem gss0:
    forall (i: positive) (x: A), get i (set0 i x) = Some x.
  Proof.
    intros i x. induction i; simpl; auto.  
  Qed.

  Theorem gos0:
    forall (i j: positive) (x: A), 
    i <> j -> get i (set0 j x) = None.
  Proof.
    induction i; intros j x H; simpl.
    - destruct j; simpl; [apply IHi; now intros <-| |]; apply gempty.
    - destruct j; simpl; [| apply IHi; now intros <-|]; apply gempty.
    - destruct j; now simpl.
  Qed.


  Theorem gss: 
    forall (i: positive) (x: A) (t: tree), get i (set i x t) = Some x.
  Proof.
    induction i; destruct t; simpl; auto; try apply IHi; now rewrite gss0.
  Qed.

  Theorem gso:
    forall (i j: positive) (x: A) (t: tree),
    i <> j -> get i (set j x t) = get i t.
  Proof.
    induction i; intros j x t H; destruct j, t;
    try auto using go0s; try apply gempty; try easy.
    - apply gos0. assumption.
    - apply IHi. now intros <-.
    - apply gos0. assumption.
    - apply IHi. now intros <-.
  Qed.

End Radix.

Arguments tree A : clear implicits.

Let radix': tree positive := empty.
Let radix'2 := set 2 2 radix'.
Compute get 2 radix'2.

