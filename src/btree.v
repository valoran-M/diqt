Require Import Coq.Array.PArray.
Require Import Coq.Init.Nat.
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.

Let array := make 6 1%nat.

Let array2 := set array 2 2%nat.

Compute (get array2 2).

