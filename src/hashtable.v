Require Import Coq.Array.PArray.
Require Import Coq.Init.Nat.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Numbers.Cyclic.Int63.Sint63.
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.


Let array := make 6 1%nat.

Let array2 := set array 2 2%nat.

Compute (get array2 2).

Open Scope int63_scope.
Open Scope sint63_scope.

Section Hashtable.
  Context {A B: Set}.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).

  Variable hash: A -> int.

  Definition bucket := list (A * B).
  Definition table := PArray.array bucket.
  
  (* Inductive hashtab : Set := hash_tab : int -> table -> hashtab. *)
  Record t : Set := hash_tab { capacity : int; size : int; hashtab : table }.

  Fixpoint power_2_above' (n: nat) (x p :int) {struct n} : int :=
    match n with
    | O   => p
    | S n => if (p <? x) 
             then power_2_above' n x (p * 2)
             else p
    end.
  
  (* 2**22 - 1 = max_length *)
  Definition power_2_above := power_2_above' 22%nat.

  Definition create (initial_size: int) : t :=
    let size := power_2_above initial_size 16 in
    hash_tab size 0 (make size []).

  Definition key_index (h: t) (k: A) :=
    (hash k) land (PArray.length (hashtab h) - 1).

  Definition add (h: t) (key: A) (v: B) :=
    let tab := hashtab h in
    let i := key_index h key in
    let bucket := get tab i in
    set tab i ((key, v) :: bucket).

  Fixpoint find_rec (l: bucket) (key: A) : option B :=
    match l with
    | [] => None
    | (k', v) :: l' => if eq k' key then Some v else find_rec l' key
    end.

  Definition find (key: A) (h: t) : option B :=
    let i := key_index h key in
    let bucket := get (hashtab h) i in
    find_rec bucket key.

End Hashtable.


