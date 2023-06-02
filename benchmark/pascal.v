Require Import hashtable.
Require Import ZArith Bool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

Fixpoint pascal (n m: nat) : int :=
  match n, m with
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 1
  | S n', S m' => pascal n' m' + pascal n' m
  end.

Compute pascal 10 5.

Fixpoint nat_to_int (n: nat) (acc: int) : int :=
  match n with
  | O   => acc
  | S n => nat_to_int n (acc + 1)
  end.

Definition hash (n : nat) (h : int) : int :=
  nat_to_int n 0 + h.

Definition hash_couple (n: (nat * nat)) :=
  let '(n1, n2) := n in
  hash n1 (hash n2 0).



Fixpoint pascal (n m: nat) () : int :=
  match n, m with
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 1
  | S n', S m' => pascal n' m' + pascal n' m
  end.

