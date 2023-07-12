Require Import ZArith.
Require Import keys.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import List.
Require radix table.

Import ListNotations.

Open Scope uint63_scope.

(** *** HashTablePositive: Hashtable with positive key (PATRICIA tree) *)

Module HashTablePositive (T: HashP).
  Definition t := @radix.tree T.A.
  Definition create (B: Set) (_: int) : t B :=
    radix.empty T.A B.

  Definition add {B: Set} (h: t B) (k: T.A) (v: B) :=
    radix.add T.A B T.hash h k v.

  Definition find {B: Set} (h: t B) (k: T.A): option B :=
    radix.find T.A T.eq B T.hash h k.

  Definition find_all {B: Set} (h: t B) (k: T.A) : list B :=
    radix.find_all T.A T.eq B T.hash h k.

  Definition mem {B: Set} (h: t B) (k: T.A) : bool :=
    radix.mem T.A T.eq B T.hash h k.

  Definition remove {B: Set} (h: t B) (k: T.A) :=
    radix.remove T.A T.eq B T.hash h k.

  Definition replace {B: Set} (h: t B) (k: T.A) (v: B) :=
    radix.replace T.A T.eq B T.hash h k v.

  (** Facts *)

  Theorem find_spec:
    forall B (ht: t B) k,
    find ht k = List.hd_error (find_all ht k).
  Proof. intros *. apply radix.find_spec. Qed.

  Theorem find_empty:
    forall B k s, find (create B s) k = None.
  Proof. intros *. apply radix.find_empty. Qed.

  Theorem mem_spec:
    forall B (ht: t B) k v,
    (find ht k = Some v -> mem ht k = true) /\
    (find ht k = None   -> mem ht k = false).
  Proof.
    intros *.
    split; unfold mem, find, radix.mem; now intros ->.
  Qed.

  Theorem add_same:
    forall B (h: t B) k v,
    find_all (add h k v) k = v :: (find_all h k).
  Proof. intros *. apply radix.find_add_same. apply T.eq_spec. Qed.

  Theorem add_other:
    forall B (h: t B) k k' v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof. intros *. apply radix.find_add_other. apply T.eq_spec. Qed.

  Theorem remove_same:
    forall B (t: t B) k,
    find_all (remove t k) k = List.tl (find_all t k).
  Proof. intros *. apply radix.remove_same. Qed.

  Theorem remove_other:
    forall B (t: t B) k k',
    k' <> k -> find_all (remove t k) k' = find_all t k'.
  Proof. intros *. apply radix.remove_other. apply T.eq_spec. Qed.

  Theorem replace_same:
    forall B (ht: t B) k v,
    find_all (replace ht k v) k = v :: (List.tl (find_all ht k)).
  Proof. intros *. apply radix.replace_same. apply T.eq_spec. Qed.
 
  Theorem replace_other:
    forall B (ht: t B) k1 k2 v,
    k1 <> k2 -> find_all (replace ht k1 v) k2 = find_all ht k2.
  Proof. intros *. apply radix.replace_other. apply T.eq_spec. Qed.  

End HashTablePositive.

(** *** HashTable: Hashtable with PArray *)

Module HashTable (T: HashI).
  Definition t := @table.t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    @table.create T.A B initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    table.add T.hash h key v.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    table.find T.eq T.hash h key.

  Definition find_all {B: Set} (h: t B) (key: T.A) :=
    table.find_all T.eq T.hash h key.

  Definition mem {B: Set} (h: t B) (key: T.A) :=
    table.mem  T.eq T.hash h key.

  Definition remove {B: Set} (h: t B) (key: T.A) :=
    table.remove T.eq T.hash h key.

  Definition replace {B: Set} (h: t B) (key: T.A) (v: B) :=
    table.replace T.eq T.hash h key v.

  (** Facts *)

  Theorem find_spec:
    forall B (ht: t B) key,
    find ht key = List.hd_error (find_all ht key).
  Proof. intros. apply table.find_spec. Qed.

  Theorem find_empty:
    forall B k s, find (create B s) k = None. 
  Proof. intros. apply table.hempty. Qed.

  Theorem mem_spec:
    forall B (ht: t B) key v,
    (find ht key = Some v -> mem ht key = true) /\
    (find ht key = None   -> mem ht key = false).
  Proof.
    intros *.
    split; unfold mem, find, table.mem; now intros ->.
  Qed.

  Theorem add_same:
    forall B (h: t B) k v,
    find_all (add h k v) k = v :: (find_all h k).
  Proof. intros. apply table.find_add_same, T.eq_spec. Qed.

  Theorem add_other:
    forall B (h: t B) k k' v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof.
    intros *. apply table.find_add_other. apply T.eq_spec.
  Qed.

  Theorem remove_same:
    forall B (t: t B) k,
    find_all (remove t k) k = List.tl (find_all t k).
  Proof. intros *. apply table.remove_same. Qed.

  Theorem remove_other:
    forall B (t: t B) k k',
    k' <> k -> find_all (remove t k) k' = find_all t k'.
  Proof. intros *. apply table.remove_other. apply T.eq_spec. Qed.

  Theorem replace_other:
    forall B (ht: t B) k1 k2 v,
    k1 <> k2 -> find_all (replace ht k1 v) k2 = find_all ht k2.
  Proof. intros *. apply table.replace_other. apply T.eq_spec. Qed.  

End HashTable.

