Require Import Bool.
Require Import ZArith.
Require dict hashtable.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

Module Type Hash_type.
  Parameter A: Set.
  Parameter eq: A -> A -> bool.
  Parameter eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Parameter hashp: A -> positive.
  Parameter hashi: A -> int.
End Hash_type.

Module Type HashTable (T : Hash_type).
  Parameter t: Set -> Type.
  Parameter create : forall {b: Set}, int -> t b.
  Parameter add : forall {b:Set}, t b -> T.A -> b -> t b.
  Parameter find : forall {b:Set}, t b -> T.A -> option b.
End HashTable.

Module HashTableTree (T: Hash_type) <: HashTable T.
  Definition t := @dict.t T.A.
  Definition create (B: Set) (_: int) : t B :=
    dict.empty T.A B.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    dict.add T.A B T.hashp key v h.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    dict.find T.A T.eq B T.hashp key h.
End HashTableTree.

Module HashTableBucket (T: Hash_type) <: HashTable T.
  Definition t := @hashtable.t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    @hashtable.create T.A B initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    hashtable.add T.hashi h key v.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    hashtable.find T.eq T.hashi h key.
End HashTableBucket.

