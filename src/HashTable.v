Require Import Keys.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import List.
Require Radix Table.

Import ListNotations.

Open Scope uint63_scope.

(** *** HashTable: Hashtable with PArray *)

Module HashTable (T: HashI).
  Definition t := @Table.t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    @Table.create T.A B initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    Table.add T.hash h key v.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    Table.find T.eq T.hash h key.

  Definition find_all {B: Set} (h: t B) (key: T.A) :=
    Table.find_all T.eq T.hash h key.

  Definition mem {B: Set} (h: t B) (key: T.A) :=
    Table.mem  T.eq T.hash h key.

  Definition remove {B: Set} (h: t B) (key: T.A) :=
    Table.remove T.eq T.hash h key.

  Definition replace {B: Set} (h: t B) (key: T.A) (v: B) :=
    Table.replace T.eq T.hash h key v.

  (** Facts *)

  Theorem find_spec:
    forall B (ht: t B) key,
    find ht key = List.hd_error (find_all ht key).
  Proof. intros. apply Table.find_spec. Qed.

  Theorem find_empty:
    forall B k s, find (create B s) k = None.
  Proof. intros. apply Table.hempty. Qed.

  Theorem mem_spec:
    forall B (ht: t B) key v,
    (find ht key = Some v -> mem ht key = true) /\
    (find ht key = None   -> mem ht key = false).
  Proof.
    intros *.
    split; unfold mem, find, Table.mem; now intros ->.
  Qed.

  Theorem add_same:
    forall B (h: t B) k v,
    find_all (add h k v) k = v :: (find_all h k).
  Proof. intros. apply Table.find_add_same, T.eq_spec. Qed.

  Theorem add_other:
    forall B (h: t B) k k' v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof. intros *. apply Table.find_add_other. apply T.eq_spec. Qed.

  Theorem remove_same:
    forall B (t: t B) k,
    find_all (remove t k) k = List.tl (find_all t k).
  Proof. intros *. apply Table.remove_same. Qed.

  Theorem remove_other:
    forall B (t: t B) k k',
    k' <> k -> find_all (remove t k) k' = find_all t k'.
  Proof. intros *. apply Table.remove_other. apply T.eq_spec. Qed.

  Theorem replace_other:
    forall B (ht: t B) k1 k2 v,
    k1 <> k2 -> find_all (replace ht k1 v) k2 = find_all ht k2.
  Proof. intros *. apply Table.replace_other. apply T.eq_spec. Qed.

End HashTable.

