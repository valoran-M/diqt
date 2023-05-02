Require Import ZArith.
Require Import tree.

Module RADIX <: TREE.
  Definition elt := positive.
  Definition elt_eq := Pos.eq_dec.

  Inductive tree (A: Type) : Type :=
  | Empty: tree A
  | Node:  tree A -> option A -> tree A -> tree A.

  Definition t := tree.

  Arguments Empty {A}.
  Arguments Node  {A} _ _.

  Definition empty (A: Type) : tree A := Empty.
  
  Fixpoint get {A} (p: positive) (t: tree A) : option A :=
    match p, t with
    | _,     Empty      => None
    | xH,    Node _ e _ => e
    | xO p', Node l _ _ => get p' l
    | xI p', Node _ _ r => get p' r
    end.

  Fixpoint set0 {A} (p: positive) (e: A) : tree A :=
    match p with
    | xH    => Node Empty (Some e) Empty
    | xO p' => Node (set0 p' e) None Empty
    | xI p' => Node Empty None (set0 p' e)
    end.

  Fixpoint set {A} (p: positive) (e: A) (t: tree A) : tree A :=
    match p, t with
    | _,     Empty      => set0 p e
    | xH,    Node l _ r => Node l (Some e) r
    | xO p', Node l y r => Node (set p' e l) y r
    | xI p', Node l y r => Node l y (set p' e r)
    end.

  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros A i. case i; reflexivity.
  Qed.

  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (t: t A), get i (set i x t) = Some x.
  Proof. Admitted.
End RADIX.

Open Scope positive_scope.

Let radix := RADIX.empty positive.
Let radix2 := RADIX.set 2 2 radix.
Compute RADIX.get 2 radix2.
