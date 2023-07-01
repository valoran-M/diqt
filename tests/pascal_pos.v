Require Import hashtable dict module utils.
Require Import ZArith Bool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Coq.FSets.FMapAVL.

Open Scope Z_scope.

(* int couple *)

Inductive zz :=
  | I : Z -> Z -> zz.

Definition eqb_pp (n m: zz) :=
  let (n1, n2) := n in
  let (m1, m2) := m in
  (n1 =? m1) && (n2 =? m2).

Theorem eq_spec_pp:
  forall n m : zz, reflect (n = m) (eqb_pp n m).
Proof.
  intros [n1 n2] [m1 m2]. case (eqb_pp _ _) eqn:H.
  + apply ReflectT. unfold eqb_pp in H.
    rewrite andb_true_iff in H. destruct H as [H1 H2].
    apply Z.eqb_eq in H1, H2. now rewrite H1, H2.
  + apply ReflectF. unfold eqb_pp in H.
    rewrite andb_false_iff in H.
    destruct H as [H | H];
    intros H0; rewrite Z.eqb_neq in H; apply H;
    now inversion H0.
Qed.

(* zz hash funtion *)

Module ZZ <: Hash_type.
  Definition A := zz.
  Definition eq n m := eqb_pp n m.
  Definition eq_spec := eq_spec_pp.
  Definition hashi (i: A): int :=
    let (n1, n2) := i in
    (of_Z n1) + (of_Z n2) * 345.

  Definition hashp (i: A): positive :=
    let (n1, n2) := i in
    match n1, n2 with
    | Zpos p1, Zpos p2 => p1 + p2 * 345
    | Zpos p1, _       => p1
    | _      , Zpos p2 => p2 * 345
    | _      , _       => 1
    end.
End ZZ.

Module PTest (H: HashTable ZZ).

  Fixpoint pascal_memo' (n m: Z) (h: H.t Z) : (Z * H.t Z) :=
    match H.find h (I n m) with
    | Some v => (v, h)
    | None =>
      match n, m with
      | Zneg _, Zneg _ 
      | Zneg _, _ | _, Zneg _ => (0, h)
      | 0, 0 => (1, h)
      | 0, _ => (0, h)
      | _, 0 => (1, h)
      | _, _ =>
          let (v1, h1) := pascal_memo' (n-1) (m-1) h in
          let (v2, h2) := pascal_memo' (n-1)  m h1 in
          let r := v1 + v2 in
          (r, H.add h2 (I n m) r)
      end
    end.

  Definition pascal_memo n m :=
    fst (pascal_memo' (Z.to_nat n) (Z.to_nat m) (of_Z n) (of_Z m) (H.create int 16)).

End PTest.

(* Pascal memo with tuple of nat *)

Module NTest (H: HashTable NATNAT).

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
    fst (pascal_memo' (Z.to_nat n) (Z.to_nat m) (H.create int 16)).

  Theorem pascal_memo_correct:
    forall n m,
    pascal_memo (Z.of_nat n) (Z.of_nat m) = pascal n m.
  Proof.
    intros n m. unfold pascal_memo.
    rewrite 2!Nat2Z.id.
    set (ok ht := forall n' m' i, H.find ht (N n' m') = Some i -> i = pascal n' m').
    cut (forall ht, ok ht -> ok (snd (pascal_memo' n m ht))
          /\ fst (pascal_memo' n m ht) = pascal n m). intros H.
    apply H. unfold ok. intros n' m' i.
    rewrite H.hempty. easy.
    revert m. induction n.
    + intros [| m] ht Hht; simpl.
      - case H.find eqn:Hf. simpl. split. easy.
        unfold ok in Hht. rewrite (Hht 0%nat 0%nat) at 1. reflexivity.
        easy. simpl. easy.
      - case H.find eqn:Hf. simpl. split. easy.
        unfold ok in Hht. rewrite (Hht 0%nat (S m)) at 1. reflexivity.
        easy. simpl. easy.
    + intros [| m] ht Oht.
      - simpl. case H.find eqn:Heq.
        simpl.
        split. easy. unfold ok in Oht. apply (Oht (S n) 0%nat). easy.
        easy.
      - simpl. case H.find eqn:Heq. simpl. split. easy.
        unfold ok in Oht. apply (Oht (S n) (S m)). easy.
        generalize (IHn m ht). destruct (pascal_memo' n m ht).
        generalize (IHn (S m) t). destruct (pascal_memo' n (S m) t).
        simpl. intros Hm Hsm.
        specialize (Hsm Oht) as [Ot ->]. specialize (Hm Ot) as [Ot0 ->].
        split. 2: reflexivity.
        intros n' m' i'.
        case (NATNAT.eq (N n' m') (N (S n) (S m))) eqn:Hnn; rewrite H.find_spec.
        * unfold NATNAT.eq in Hnn.
          case (NATNAT.eq_spec (N n' m') (N (S n) (S m))) as [Hn|] in Hnn.
          2:discriminate. rewrite Hn, H.add_same.
          simpl. injection Hn. intros -> ->. simpl. intros H. injection H.
          intros <-. reflexivity.
        * rewrite H.add_diff. intros Hf. rewrite (Ot0 n' m') at 1.
          reflexivity. rewrite H.find_spec. easy.
          unfold NATNAT.eq in Hnn.
          case (NATNAT.eq_spec (N n' m') (N (S n) (S m))) as [|Hn] in Hnn.
          discriminate. easy.
  Qed.

End NTest.

(* FINTINT Key type for FMap AVL in stdlib *)

Module FINTINT.
  Definition t := intint.
  Definition eq (n m: t) := eqb_pp n m = true.

  Lemma eq_refl:
    forall i, eq i i.
  Proof.
    unfold eq, eqb_pp. intros [n1 n2].
    rewrite 2!eqb_refl. reflexivity.
  Qed.

  Lemma eq_sym:
    forall n m : t, eq n m -> eq m n.
  Proof.
    intros [n1 n2] [m1 m2].
    unfold eq, eqb_pp. intros H.
    apply andb_true_intro. rewrite andb_true_iff in H.
    rewrite 2!eqb_spec in H. destruct H as [<- <-].
    rewrite 2!eqb_refl. easy.
  Qed.

  Lemma eq_trans:
    forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros [x1 x2] [y1 y2] [z1 z2] Hxy Hyz.
    unfold eq, eqb_pp in *.
    rewrite andb_true_iff, 2!eqb_spec in *.
    now destruct Hxy as [<- <-].
  Qed.

  Definition eq_spec := eq_spec_ii.

  (* Lexicographic order *)
  Definition lt (n m: t) :=
    let (n1, n2) := n in
    let (m1, m2) := m in
    (n1 <? m1) || ((n1 =? m1) && (n2 <? m2)) = true.

  Lemma lt_trans:
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros [x1 x2] [y1 y2] [z1 z2] Hxy Hyz.
    unfold lt in *.
    rewrite orb_true_iff, andb_true_iff,
            2!ltb_spec, eqb_spec in *.
    destruct Hxy as [Hxy1 | [Heq1 Hxy2]].
    + destruct Hyz as [Hyz1 | [Heq2 Hyz2]].
      - left. now apply Z.lt_trans with (m:=to_Z y1).
      - rewrite <- Heq2. now left.
    + destruct Hyz as [Hyz1 | [Heq2 Hyz2]].
      - rewrite Heq1. now left.
      - rewrite Heq1, Heq2. right. split. reflexivity.
        now apply Z.lt_trans with (m:=to_Z y2).
  Qed.

  Lemma lt_not_eq:
    forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros [x1 x2] [y1 y2] Hlt Heq.
    unfold eq, eqb_pp in Heq. rewrite andb_true_iff, 2!eqb_spec in Heq.
    destruct Heq as [<- <-].
    unfold lt in Hlt. rewrite orb_true_iff, andb_true_iff in Hlt.
    destruct Hlt as [Hlt | [_ Hlt]];
    rewrite ltb_spec in Hlt.
    + contradiction (Z.lt_irrefl (to_Z x1)).
    + contradiction (Z.lt_irrefl (to_Z x2)).
  Qed.

  Definition compare_def (x y: t) :=
    let (x1, x2) := x in
    let (y1, y2) := y in
    let cmp := compare x1 y1 in
    match cmp with
    | Eq => compare x2 y2
    | _ => cmp
    end.

  Lemma compare_eq:
    forall x y, compare_def x y = Eq -> eq x y.
  Proof.
    intros [x1 x2] [y1 y2] H.
    unfold compare_def in H.
    unfold eq, eqb_pp.
    apply andb_true_iff. rewrite 2!eqbP_true_to_Z.
    case (x1 ?= y1) eqn:H1; try discriminate.
    rewrite compare_spec in *.
    split; now apply Z.compare_eq.
  Qed.

  Lemma compare_lt:
    forall x y, compare_def x y = Lt -> lt x y.
  Proof.
    intros [x1 x2] [y1 y2] H.
    unfold compare_def in H. unfold lt.
    apply orb_true_iff. rewrite andb_true_iff, eqbP_true_to_Z.
    case (x1 ?= y1) eqn:H1; try discriminate.
    + rewrite compare_spec in *. right. split.
      now apply Z.compare_eq in H1.
      apply ltb_spec. now rewrite <- Z.compare_lt_iff.
    + left. rewrite compare_spec in H1. rewrite ltb_spec.
      now rewrite <- Z.compare_lt_iff.
  Qed.

  Lemma compare_gt:
    forall x y, compare_def x y = Gt -> lt y x.
  Proof.
    intros [x1 x2] [y1 y2] H.
    unfold compare_def in H. unfold lt.
    apply orb_true_iff. rewrite andb_true_iff, eqbP_true_to_Z.
    case (x1 ?= y1) eqn:H1; try discriminate.
    + right. rewrite compare_spec in *. split.
      now apply Z.compare_eq in H1.
      rewrite Zcompare_Gt_Lt_antisym in H.
      apply ltb_spec. now rewrite <- Z.compare_lt_iff.
    + left. rewrite compare_spec in *.
      rewrite Zcompare_Gt_Lt_antisym in H1.
      apply ltb_spec. now rewrite <- Z.compare_lt_iff.
  Qed.

  Definition compare (x y: t):
    OrderedType.Compare lt eq x y.
  Proof.
    case (compare_def x y) eqn:Hc.
    + apply OrderedType.EQ. now apply compare_eq.
    + apply OrderedType.LT. now apply compare_lt.
    + apply OrderedType.GT. now apply compare_gt.
  Defined.

  Definition eq_dec:
    forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros [x1 x2] [y1 y2]. unfold eq, eqb_pp.
    case (x1 =? y1) eqn:H1. case (x2 =? y2) eqn:H2.
    1:   now left.
    all: now right.
  Qed.
End FINTINT.

(* Pascal memo with tuple of int and Fmap *)

Module FTest.
  Module Import M := FMapAVL.Make(FINTINT).

  Fixpoint pascal_memo' (n m: nat) (ni mi : int) (h: M.t int) : (int * M.t int) :=
    match M.find (I ni mi) h with
    | Some v => (v, h)
    | None =>
      match n, m with
      | 0, 0 => (1, h)
      | 0, _ => (0, h)
      | _, 0 => (1, h)
      | S n', S m' =>
          let (v1, h1) := pascal_memo' n' m' (ni-1) (mi -1) h in
          let (v2, h2) := pascal_memo' n' m (ni-1) mi h1 in
          let r := v1 + v2 in
          (r, M.add (I ni mi) r h2)
      end
    end.

  Definition pascal_memo n m :=
    fst (pascal_memo' (Z.to_nat n) (Z.to_nat m) (of_Z n) (of_Z m) (M.empty int)).

End FTest.

(* tests *)

Module HTreeNN := HashTableTree NATNAT.
Module NTestTree := NTest HTreeNN.

Module HBucketNN := HashTableBucket NATNAT.
Module NTestBucket := NTest HBucketNN.

Module HTree := HashTableTree INTINT.
Module ITestTree := ITest HTree.

Module HBucket := HashTableBucket INTINT.
Module ITestBucket := ITest HBucket.

(* Time Compute ITestTree.pascal_memo 500 250. *)
(* Time Compute ITestBucket.pascal_memo 500 250. *)


(* results:

  N{Radix Tree, Bucket} = pascal memo with natnat (expensive hash)
  I{Radix Tree, Bucket} = pascal memo with intint (free hash)

   +-------------+--------+--------+--------+--------+
   | pascal 2n n | n=50   | n=100  | n=150  | n=200  |
   +-------------+--------+--------+--------+--------+
   | NRadix Tree | 0.093s | 0.331s | 0.919s | 1.917s |
   +-------------+--------+--------+--------+--------+
   | NBucket     | 0.032s | 0.167s | 0.462s | 1.003s | ~ / 2
   +-------------+--------+--------+--------+--------+
   | FMap Avl    | 0.084s | 0.35s  | 0.723s | 1.413  |
   +-------------+--------+--------+--------+--------+
   | IRadix Tree | 0.068s | 0.206s | 0.423s | 0.788s |
   +-------------+--------+--------+--------+--------+
   | IBucket     | 0.009s | 0.026s | 0.069s | 0.091s | ~ / 10
   +-------------+--------+--------+--------+--------+
*)

(*@ test_pascal
    for n : 20 -> 300
      {s
        Require Import pascal.
        Definition ii := (2 * n)%Z.
      s}
      (* FMap *)
      { Time Compute FTest.pascal_memo ii n. }
      (* NRadix *)
      { Time Compute NTestTree.pascal_memo ii n. }
      (* NBucket *)
      { Time Compute NTestBucket.pascal_memo ii n. }
      (* IRadix *)
      { Time Compute ITestTree.pascal_memo ii n. }
      (* IBucket *)
      { Time Compute ITestBucket.pascal_memo ii n. }
 @*)

