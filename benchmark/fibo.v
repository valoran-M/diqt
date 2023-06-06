Require Import hashtable.
Require Import ZArith Bool.

Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

Fixpoint fib (n : nat) : int :=
  match n with
    | 0 => 0
    | S n' => 
        match n' with
        | 0 => 1
        | S n'' => fib n' + fib n''
        end
  end.

Compute fib 10%nat.

Theorem int_eq_spec:
  forall x y : int, reflect (x = y) (eqb x y).
Proof.
  intros x y. case (eqb x y) eqn:H.
  + apply ReflectT. now apply eqb_spec.
  + apply ReflectF. now apply eqb_false_spec.
Qed.

(* Module Int <: Hash_Type. *)
(*   Definition A := int. *)
(*   Definition eq x y:= eqb x y. *)
(*   Definition eq_spec := int_eq_spec. *)
(*   Definition hash i: A := i. *)
(* End Int. *)
(**)
(* Module HashT := HashTable (Int). *)
(**)
(* Fixpoint fib_memo' (n: nat) (m: int) (h: HashT.t nat) : nat * (HashT.t nat) := *)
(*   match HashT.find h m with *)
(*   | Some v => (v, h) *)
(*   | None => *)
(*       match n with *)
(*       | 0 => (0, HashT.add h m 0)%nat *)
(*       | S n' =>  *)
(*           match n' with *)
(*           | 0 => (1, HashT.add h m 1)%nat *)
(*           | S n'' =>  *)
(*               let (v1, h1) := fib_memo' n'  (m - 1) h  in *)
(*               let (v2, h2) := fib_memo' n'' (m - 2) h1 in *)
(*               let h3 := HashT.add h2 m (v1 + v2)%nat in *)
(*               match HashT.find h3 m with *)
(*               | Some v => (v, h3) *)
(*               | None => (0, h3)%nat *)
(*               end *)
(*           end *)
(*       end *)
(*   end. *)
(**)
(* Definition fib_memo n m := fst (fib_memo' n m (HashT.create Z 16)). *)
(**)
(* Compute fib 35 35. *)
(**)
(* Compute fib_memo 35 35. *)
