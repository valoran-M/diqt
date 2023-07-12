Require Import ZArith.
Require Import Keys.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import List.
Require Radix Table.

Import ListNotations.

Open Scope uint63_scope.

(** ** HashTablePositive: Hashtable with positive key (PATRICIA tree) *)

Module HashTablePositive (T: HashP).
  Definition t := @Radix.tree T.A.
  Definition create (B: Set) (_: int) : t B :=
    Radix.empty T.A B.

  Definition add {B: Set} (h: t B) (k: T.A) (v: B) :=
    Radix.add T.A B T.hash h k v.

  Definition find {B: Set} (h: t B) (k: T.A): option B :=
    Radix.find T.A T.eq B T.hash h k.

  Definition find_all {B: Set} (h: t B) (k: T.A) : list B :=
    Radix.find_all T.A T.eq B T.hash h k.

  Definition mem {B: Set} (h: t B) (k: T.A) : bool :=
    Radix.mem T.A T.eq B T.hash h k.

  Definition remove {B: Set} (h: t B) (k: T.A) :=
    Radix.remove T.A T.eq B T.hash h k.

  Definition replace {B: Set} (h: t B) (k: T.A) (v: B) :=
    Radix.replace T.A T.eq B T.hash h k v.

  (** Facts *)

  Theorem find_spec:
    forall B (ht: t B) k,
    find ht k = List.hd_error (find_all ht k).
  Proof. intros *. apply Radix.find_spec. Qed.

  Theorem find_empty:
    forall B k s, find (create B s) k = None.
  Proof. intros *. apply Radix.find_empty. Qed.

  Theorem mem_spec:
    forall B (ht: t B) k v,
    (find ht k = Some v -> mem ht k = true) /\
    (find ht k = None   -> mem ht k = false).
  Proof.
    intros *.
    split; unfold mem, find, Radix.mem; now intros ->.
  Qed.

  Theorem add_same:
    forall B (h: t B) k v,
    find_all (add h k v) k = v :: (find_all h k).
  Proof. intros *. apply Radix.find_add_same. apply T.eq_spec. Qed.

  Theorem add_other:
    forall B (h: t B) k k' v,
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof. intros *. apply Radix.find_add_other. apply T.eq_spec. Qed.

  Theorem remove_same:
    forall B (t: t B) k,
    find_all (remove t k) k = List.tl (find_all t k).
  Proof. intros *. apply Radix.remove_same. Qed.

  Theorem remove_other:
    forall B (t: t B) k k',
    k' <> k -> find_all (remove t k) k' = find_all t k'.
  Proof. intros *. apply Radix.remove_other. apply T.eq_spec. Qed.

  Theorem replace_same:
    forall B (ht: t B) k v,
    find_all (replace ht k v) k = v :: (List.tl (find_all ht k)).
  Proof. intros *. apply Radix.replace_same. apply T.eq_spec. Qed.

  Theorem replace_other:
    forall B (ht: t B) k1 k2 v,
    k1 <> k2 -> find_all (replace ht k1 v) k2 = find_all ht k2.
  Proof. intros *. apply Radix.replace_other. apply T.eq_spec. Qed.

End HashTablePositive.


