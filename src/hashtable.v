Require Import Coq.Array.PArray.
Require Import Coq.Init.Nat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
(* Require Import Coq.Numbers.Cyclic.Int63.PrimInt63. *)

Open Scope uint63_scope.
Print int.
Check to_Z.

Section Hashtable.
  Context {A B: Set}.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable hash: A -> int.

  Lemma eq_true:
    forall (k1 k2 : A), k1 = k2 -> eq k1 k2 = true.
  Proof.
    intros k1 k2 H.
    now case eq_spec.
  Qed.

  Lemma eq_false:
    forall (k1 k2 : A), k1 <> k2 -> eq k1 k2 = false.
  Proof.
    intros k1 k2 H.
    now case eq_spec.
  Qed.

  Lemma eq_refl:
    forall (k : A), eq k k = true.
  Proof.
    intros k.
    now case eq_spec.
  Qed.

  Definition bucket := list (A * B).
  Definition table := PArray.array bucket.
  
  Record t : Set := hash_tab { 
    size : int;
    hashtab : table; 
  }.

  Fixpoint power_2_above' (n: nat) (x p: int) {struct n} : int :=
    match n with
    | O    => p
    | S n' => if (p <? x) 
             then power_2_above' n' x (p * 2)
             else p
    end.
  
  (* 2**22 - 1 = max_length *)
  Definition power_2_above := power_2_above' 22%nat.

  Definition create (initial_size: int) : t :=
    let size := power_2_above initial_size 16 in
    let h := make size [] in
    hash_tab 0 h.


  Definition key_index (h: t) (k: A) : int :=
    (hash k) land (PArray.length (hashtab h) - 1).

  Definition get_bucket (h: t) (k: A) : bucket :=
    if PArray.length (hashtab h) =? 0 then
      []
    else 
      (hashtab h).[key_index h k].

  Definition resize_heurisitic (h: t) : bool :=
    PArray.length (hashtab h) =? 0.

  Definition resize (h: t): t :=
    if PArray.length (hashtab h) =? 0 then 
      hash_tab 0 (make 16 [])
    else h.

  Lemma length_resize:
    forall (h: t),
    (0 < to_Z (PArray.length (hashtab (resize h))))%Z.
  Proof.
    admit.
  Admitted.

  Definition add (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let i := key_index h key in
    let bucket := get tab i in
    let new := (key, v) :: tab.[i] in
    hash_tab (size h + 1) tab.[i<-new].

  Fixpoint find_rec (l: bucket) (key: A) : option B :=
    match l with
    | [] => None
    | (k', v) :: l' => if eq k' key then Some v else find_rec l' key
    end.

  Fixpoint find_all_rec (l: bucket) (key: A) (acc: list B): list B :=
    match l with
    | [] => List.rev' acc
    | (k', v) :: l' => 
        if eq k' key 
        then find_all_rec l' key (v :: acc)
        else find_all_rec l' key acc
    end.

  Fixpoint find_all_rec' (l: bucket) (key: A) : list B :=
    match l with
    | [] => []
    | (k', v) :: l' => 
        if eq k' key 
        then v :: find_all_rec' l' key
        else find_all_rec' l' key
    end.

  Lemma find_all_rec_correct:
    forall (l: bucket) (key: A),
    find_all_rec l key [] = find_all_rec' l key.
  Proof.
    intros l key. 
    change (find_all_rec l key [] = rev [] ++ find_all_rec' l key).
    generalize (nil : list B). induction l.
    + intros acc. simpl. apply rev_append_rev.
    + intros acc. simpl. destruct a. case eq.
      rewrite IHl. simpl. rewrite <- app_assoc. easy.
      apply IHl.
  Qed.

  Definition find (h: t) (key: A) : option B :=
    let bucket := get_bucket h key in
    find_rec bucket key.

  Definition find_all (h: t) (key: A) : list B :=
    find_all_rec (get_bucket h key) key [].

  Lemma find_all_resize:
    forall (h: t) (k: A),
    find_all (resize h) k = find_all h k.
  Proof.
    intros h k. unfold resize, find_all, get_bucket.
    case (PArray.length (hashtab h) =? 0) eqn:Heqb.
    simpl eqb. cbn iota. unfold hashtab.
    now rewrite get_make.
    now rewrite Heqb.
  Qed.

  Theorem hempty:
    forall (k: A) (size: int), find (create size) k = None.
  Proof. Admitted.
  (*   intros k i. unfold create, find, get_bucket. simpl. *)
  (*   rewrite length_make. *)
  (*   now rewrite get_make. *)
  (* Qed. *)

  Lemma key_index_eq:
    forall (h1 h2: t) (k: A), 
    PArray.length (hashtab h1) = PArray.length (hashtab h2) ->
    key_index h1 k = key_index h2 k.
  Proof.
    intros h1 h2 k H. unfold key_index.
    now rewrite H.
  Qed.

  Theorem dadd:
    forall (k: A) (v: B) (h: t),
    find_all (add h k v) k = v::(find_all h k).
  Proof.
    intros k v h. rewrite <- (find_all_resize h).
    unfold find_all.
    rewrite 2!find_all_rec_correct.
    unfold get_bucket.
    rewrite 2!eqb_false_complete.
    rewrite (key_index_eq (add h k v) (resize h)).
    unfold add; simpl. rewrite get_set_same.
    simpl. rewrite eq_refl. easy.
    admit.
    unfold add; simpl. apply length_set.
  Admitted.

End Hashtable.

Module Type Hash_type.
  Variable A: Set.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable hash: A -> int.
End Hash_type.

Module HashTable (T: Hash_type).
  Definition t := @t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    create initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    add T.hash h key v.

  Definition find {B: Set} (h: t B) (key: T.A): option B :=
    find T.eq T.hash key h.
End HashTable.

