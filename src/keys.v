Require Import Bool ZArith.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

(** Keys modules *)

Module Type Eq.
  Parameter A: Set.
  Parameter eq: A -> A -> bool.
  Parameter eq_spec: forall x y : A, reflect (x = y) (eq x y).
End Eq.

Module Type HashP.
  Include Eq.
  Parameter hash: A -> positive.
End HashP.

Module Type HashI.
  Include Eq.
  Parameter hash: A -> int.
End HashI.

