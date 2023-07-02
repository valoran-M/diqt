Require Import ZArith Bool.
Require Import module hashtable utils.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Coq.FSets.FMapAVL.

Open Scope uint63_scope.

Definition f k i :=
  if (i =? 500000000)%Z then
    true
  else
    k (i + 1)%Z.

Definition g :=
  Pos.iter f (fun _ => false) 10000000 0%Z.

(*
h <- []
for i = 1 to +inf
    if (i in h) then (h <- h \ {i}; continue)
    j <- i
    while true do
        j <- syracuse j
        if j < i then break
        match h.[j] with
        | Some i' => if i = i' then return else break
        | None    => h <- h.[j <- i]
    done
*)

Definition syracuse (n: int) :=
  if n land 1 =? 0
  then n >> 1
  else (3 * n + 1) >> 1.

Module INT <: Hash_type.
  Definition A := int.
  Definition eq n m := eqb n m.
  Definition eq_spec:
    forall n m, reflect (n = m) (eqb n m).
  Proof.
    intros n m. case (n =? m) eqn:H.
    + apply ReflectT. now apply eqb_spec.
    + apply ReflectF. now apply eqb_false_spec.
  Qed.

  Definition hashi (i: A): int := i.

  Definition hashp (i: A): positive :=
    match to_Z i with
    | Z.pos i => i
    | _ => xH
    end.
End INT.

Module Test (H: HashTable INT).

  Inductive syracuse_ret :=
    | Ok       : syracuse_ret
    | Overflow : int -> syracuse_ret
    | TimeOut  : int -> syracuse_ret
    | Loop     : int -> syracuse_ret.

  Definition while k (h: H.t int) (j': int) (i: int) :=
    if 3074457345618258602 <? j' then (h, Overflow j')
    else
      let j := syracuse j' in
      if j <? i then (h, Ok)
      else
        match H.find h j with
        | Some i' => if i =? i' then (h, Loop i) else (h, Ok)
        | None    => k (H.add h j i) j i
        end.

  Definition for_i k (h: H.t int) (i: int) :=
    if H.mem h i || (i =? 1) then
      k (H.remove h i) (i + 1)
    else
      match Pos.iter while (fun h _ _ => (h, TimeOut i)) 1000 h i i with
      | (h, Ok) => k h (i + 1)
      | x       => x
      end.

  Definition syracuse_launch n :=
    snd (Pos.iter for_i (fun h _ => (h, Ok)) n (H.create int 16) 1).

End Test.

Module FINT.
  Definition t := int.
  Definition eq (n m: t) := eq n m.

  Lemma eq_refl:
    forall i, eq i i.
  Proof.
    unfold eq. intros i. apply eqb_spec, eqb_refl.
  Qed.

  Lemma eq_sym:
    forall n m : t, eq n m -> eq m n.
  Proof.
    unfold eq. now intros n m ->.
  Qed.

  Lemma eq_trans:
    forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. now intros x y z <- <-.
  Qed.

  Definition eq_spec:
    forall n m : int, reflect (n = m) (eqb n m).
  Proof.
    intros n m. case (n =? m) eqn: Hn.
    + apply ReflectT. now apply eqb_spec in Hn.
    + apply ReflectF. now apply eqb_false_spec in Hn.
  Qed.

  Definition lt (n m: t) := n <? m = true.

  Lemma lt_trans:
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    intros x y z Hxy Hyz. rewrite ltb_spec in *.
    now apply Z.lt_trans with (to_Z y).
  Qed.

  Lemma lt_not_eq:
    forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq. intros x y H.
    apply ltb_spec in H. rewrite <- eqb_false_spec.
    rewrite eqbP_false_to_Z. intros Heq. rewrite Heq in H.
    exact (Z.lt_irrefl (to_Z y) H).
  Qed.

  Lemma compe_eq:
    forall x y, compare_def x y = Eq -> eq x y.
  Proof.
    intros x y. unfold compare_def.
    case (x <? y). easy. case (x =? y) eqn:H.
    rewrite eqb_spec in H. easy.
    easy.
  Qed.

  Lemma compe_lt:
    forall x y, compare_def x y = Lt -> lt x y.
  Proof.
    intros x y. unfold compare_def.
    case (x <? y) eqn:H. now unfold lt.
    case (x =? y); easy.
  Qed.

  Lemma compe_gt:
    forall x y, compare_def x y = Gt -> lt y x.
  Proof.
    intros x y. unfold compare_def.
    case (x <? y) eqn:Hlt; case (x =? y) eqn:Heq; try discriminate.
    unfold lt. rewrite ltb_spec.
    case (ltbP x y) in Hlt. discriminate.
    apply eqbP_false_to_Z in Heq.
    rewrite Z.nlt_ge in n. intros _. apply Z.le_neq. split. easy.
    intros H. now apply Heq.
  Qed.

  Definition compare (x y: t):
    OrderedType.Compare lt eq x y.
  Proof.
    case (compare_def x y) eqn:Hc.
    + apply OrderedType.EQ. now apply compe_eq.
    + apply OrderedType.LT. now apply compe_lt.
    + apply OrderedType.GT. now apply compe_gt.
  Defined.

  Definition eq_dec:
    forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y. unfold eq.
    case (x =? y) eqn:H.
    + apply eqb_spec in H. now left.
    + rewrite eqb_false_spec in H. now right.
  Qed.

End FINT.

Module FTest.
  Module Import M := FMapAVL.Make(FINT).

  Inductive syracuse_ret :=
    | Ok       : syracuse_ret
    | Overflow : int -> syracuse_ret
    | TimeOut  : int -> syracuse_ret
    | Loop     : int -> syracuse_ret.

  Definition while k (h: M.t int) (j': int) (i: int) :=
    if 3074457345618258602 <? j' then (h, Overflow j')
    else
      let j := syracuse j' in
      if j <? i then (h, Ok)
      else
        match M.find j h with
        | Some i' => if i =? i' then (h, Loop i) else (h, Ok)
        | None    => k (M.add j i h) j i
        end.

  Definition for_i k (h: M.t int) (i: int) :=
    if M.mem i h || (i =? 1) then
      k (M.remove i h) (i + 1)
    else
      match Pos.iter while (fun h _ _ => (h, TimeOut i)) 1000 h i i with
      | (h, Ok) => k h (i + 1)
      | x       => x
      end.

  Definition syracuse_launch n :=
    snd (Pos.iter for_i (fun h _ => (h, Ok)) n (M.empty int) 1).

End FTest.

Module HTree := HashTableTree INT.
Module ITestTree := Test HTree.

Module HBucket := HashTableBucket INT.
Module ITestBucket := Test HBucket.

(*@ test_syracuse
    for i : 100 -> 100000
      {s
        Require Import syracuse syracuse_pos.
        Let n := Z.to_pos i.
      s}
      (* FMap_AVL *)
      { Time Compute FTest.syracuse_launch n. }
      (* IRadix *)
      { Time Compute ITestTree.syracuse_launch n. }
      (* IBucket *)
      { Time Compute ITestBucket.syracuse_launch n. }
      (* FMap_Pos *)
      { Time Compute FPTest.syracuse_launch n. }
      (* PRadix *)
      { Time Compute PTestTree.syracuse_launch n. }
      (* PBucket *)
      { Time Compute PTestBucket.syracuse_launch n. }
 @*)

(*
   +-------------+--------+--------+--------+----------+----------+
   | syracuse n  | n=100  | n=1000 | n=10000| n=100000 | n=1000000|
   +-------------+--------+--------+--------+----------+----------+
   | FMap Avl    | 0.004s | 0.044s | 0.403s | 3.87s    | 48.856s  |
   +-------------+--------+--------+--------+----------+----------+
   | IRadix Tree | 0.005s | 0.049s | 0.241s | 2.44s    | 29.237s  |
   +-------------+--------+--------+--------+----------+----------+
   | IBucket     | 0.003s | 0.021s | 0.146s | 1.243s   | 13.101s  | ~ / 10
   +-------------+--------+--------+--------+----------+----------+
*)

