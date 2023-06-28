Require Import Bool.
Require Import ZArith.
Require dict hashtable.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import List.

Import ListNotations.

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
  Parameter create : forall B: Set, int -> t B.
  Parameter add : forall {B:Set}, t B -> T.A -> B -> t B.
  Parameter find : forall {B:Set}, t B -> T.A -> option B.
  Parameter find_all: forall {B: Set}, t B -> T.A -> list B.
  Parameter mem: forall {B: Set}, t B -> T.A -> bool.
  Parameter remove: forall {B: Set}, t B -> T.A -> t B.
  Parameter replace: forall {B: Set}, t B -> T.A -> B -> t B.

  Parameter find_spec:
    forall B (ht: t B) key,
    find ht key = List.hd_error (find_all ht key).

  Parameter hempty:
    forall B k s, find (create B s) k = None.

  Parameter add_same:
    forall B k (h: t B) v,
    find_all (add h k v) k = v :: (find_all h k).

  Parameter add_diff:
    forall B k k' (h: t B) v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
End HashTable.

Module HashTableTree (T: Hash_type) <: HashTable T.
  Definition t := @dict.t T.A.
  Definition create (B: Set) (_: int) : t B :=
    dict.empty T.A B.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    dict.add T.A B T.hashp key v h.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    dict.find T.A T.eq B T.hashp key h.

  Definition find_all {B: Set} (h: t B) (key: T.A) : list B :=
    dict.find_all T.A T.eq B T.hashp key h.

  Definition remove {B: Set} (h: t B) (key: T.A) :=
    dict.remove T.A T.eq B T.hashp key h.

  Definition replace {B: Set} (h: t B) (key: T.A) (v: B) :=
    dict.replace T.A T.eq B T.hashp key v h.

  Definition mem {B: Set} (h: t B) (key: T.A) : bool :=
    match find h key with
    | Some _ => true
    | None   => false
    end.

  Theorem find_spec:
    forall B (ht: t B) key,
    find ht key = List.hd_error (find_all ht key).
  Admitted.

  Theorem hempty:
    forall B k s, find (create B s) k = None.
  Admitted.

  Theorem add_same:
    forall B k (h: t B) v,
    find_all (add h k v) k = v :: (find_all h k).
  Admitted.

  Theorem add_diff:
    forall B k k' (h: t B) v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Admitted.
End HashTableTree.

Module HashTableBucket (T: Hash_type) <: HashTable T.
  Definition t := @hashtable.t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    @hashtable.create T.A B initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    hashtable.add T.hashi h key v.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    hashtable.find T.eq T.hashi h key.

  Definition find_all {B: Set} (h: t B) (key: T.A) :=
    hashtable.find_all T.eq T.hashi h key.

  Definition mem {B: Set} (h: t B) (key: T.A) :=
    hashtable.mem  T.eq T.hashi h key.

  Definition remove {B: Set} (h: t B) (key: T.A) :=
    hashtable.remove T.eq T.hashi h key.

  Definition replace {B: Set} (h: t B) (key: T.A) (v: B) :=
    hashtable.replace T.eq T.hashi h key v.

  Theorem find_spec:
    forall B (ht: t B) key,
    find ht key = List.hd_error (find_all ht key).
  Proof. intros. apply hashtable.find_spec. Qed.

  Theorem hempty:
    forall B k s, find (create B s) k = None. 
  Proof. intros. apply hashtable.hempty. Qed.

  Theorem add_same:
    forall B k (h: t B) v,
    find_all (add h k v) k = v :: (find_all h k).
  Proof. intros. apply hashtable.find_add_same, T.eq_spec. Qed.

  Theorem add_diff:
    forall B k k' (h: t B) v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof.
    intros B k k' h v H.
    apply hashtable.find_add_diff.
    apply T.eq_spec. apply H.
  Qed.

End HashTableBucket.

