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

  Definition t := PArray.array (list (A * B)).

  Print max_length.

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
    make size [].

  Definition key_index (h: t) (k: A) :=
    (hash k) land (PArray.length h - 1).

  Definition add (key: A) (v: B) (h: t) :=
    let i := key_index h key in
    let bucket := get h i in
    set h i ((key, v) :: bucket).

  Fixpoint find_rec (l: list (A * B)) (key: A) : option B :=
    match l with
    | [] => None
    | (k', v) :: l' => if eq k' key then Some v else find_rec l' key
    end.

  Definition find (key: A) (h: t) : option B :=
    let i := key_index h key in
    let bucket := get h i in
    find_rec bucket key.

End Hashtable.


