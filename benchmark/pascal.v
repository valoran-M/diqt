Require Import hashtable dict module.
Require Import ZArith Bool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

Fixpoint pascal (n m: nat) : int :=
  match n, m with
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 1
  | S n', S m' => pascal n' m' + pascal n' m
  end.

Inductive natnat :=
  | N : nat -> nat -> natnat.

Fixpoint nat_to_int (n: nat) (acc: int) : int :=
  match n with
  | O   => acc
  | S n => nat_to_int n (acc + 1)
  end.

Definition hash (n : nat) (h : int) : int :=
  nat_to_int n 0 + h * 345.

Definition eqb_nn (n m: natnat) :=
  let (n1, n2) := n in
  let (m1, m2) := m in
  (n1 =? m1)%nat && (n2 =? m2)%nat.

Theorem eq_spec:
  forall n m : natnat, reflect (n = m) (eqb_nn n m).
Proof.
  intros [n1 n2] [m1 m2]. case (eqb_nn _ _) eqn:H.
  + apply ReflectT. unfold eqb_nn in H.
    rewrite andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.eqb_eq in H1, H2. now rewrite H1, H2.
  + apply ReflectF. unfold eqb_nn in H.
    rewrite andb_false_iff in H. destruct H as [H | H];
    intros H0; rewrite Nat.eqb_neq in H; apply H; 
    now inversion H0.
Qed.

Module NATNAT <: Hash_type.
  Definition A := natnat.
  Definition eq n m := eqb_nn n m.
  Definition eq_spec := eq_spec.
  Definition hashi (i: natnat): int :=
    let (n1, n2) := i in
    hash n1 (hash n2 0).
  Definition hashp (i: natnat): positive :=
    let hi := hashi i in
    match to_Z hi with
    | Z.pos p => p
    | _ => xH
    end.
End NATNAT.

Module Test (H: HashTable NATNAT).

  Fixpoint pascal_memo' (n m: nat) (h: H.t int) : (int * H.t int) :=
    match H.find h (N n m) with
    | Some v => (v, h)
    | None =>
      match n, m with
      | 0, 0 => (1, h)
      | 0, _ => (0, h)
      | _, 0 => (1, h) 
      | S n', S m' => 
        let (v1, h1) := pascal_memo' n' m' h in
        let (v2, h2) := pascal_memo' n' m h1 in
        let r := v1 + v2 in
        (r, H.add h2 (N n m) r) 
      end
    end.

  Definition pascal_memo n m :=
    fst (pascal_memo' n m (H.create 16)).

End Test.

Module HTree := HashTableTree NATNAT.
Module TestTree := Test HTree.

Module HBucket := HashTableBucket NATNAT.
Module TestBucket := Test HBucket.

(* Compute pascal 30 15. *)
Time Compute TestTree.pascal_memo 400 200.
Time Compute TestBucket.pascal_memo 400 200.

(* +-------------+--------+--------+--------+--------+
   | pascal 2n n | n=50   | n=100  | n=150  | n=200  | 
   +-------------+--------+--------+--------+--------+
   | Radix Tree  | 0.093s | 0.331s | 0.919s | 1.917s |
   +-------------+--------+--------+--------+--------+
   | Bucket      | 0.032s | 0.167s | 0.462s | 1.003s | ~ / 2
   +-------------+--------+--------+--------+--------+
*)

