Require Import module hashtable utils.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Coq.FSets.FMapAVL FMapPositive.
Require Import ZArith Bool.

Open Scope positive_scope.

Definition syracuse (n: positive) :=
  match n with
  | xO n' => n'
  | _ => (3 * n + 1)
  end.

Module POS <: Hash_type.
  Definition A := positive.
  Definition eq n m := Pos.eqb n m.
  Definition eq_spec := Pos.eqb_spec.

  Definition hashi (i: A): int :=
    of_Z (Z.pos i).

  Definition hashp (i: A): positive := i.
End POS.

Module Test (H: HashTable POS).

  Inductive syracuse_ret :=
    | Ok       : syracuse_ret
    | TimeOut  : positive -> syracuse_ret
    | Loop     : positive -> syracuse_ret.

  Definition while k (h: H.t positive) (j': positive) (i: positive) :=
      let j := syracuse j' in
      if j <? i then (h, Ok)
      else
        match H.find h j with
        | Some i' => if i =? i' then (h, Loop i) else (h, Ok)
        | None    => k (H.add h j i) j i
        end.

  Definition for_i k (h: H.t positive) (i: positive) :=
    if H.mem h i || (i =? 1) then
      k (H.remove h i) (i + 1)
    else
      match Pos.iter while (fun h _ _ => (h, TimeOut i)) 1000 h i i with
      | (h, Ok) => k h (i + 1)
      | x       => x
      end.

  Definition syracuse_launch n :=
    Pos.iter for_i (fun h _ => (h, Ok)) n (H.create positive 16) 1.

End Test.

Module FTest.
  Module Import H := PositiveMap.

  Inductive syracuse_ret :=
    | Ok       : syracuse_ret
    | TimeOut  : positive -> syracuse_ret
    | Loop     : positive -> syracuse_ret.

  Definition while k (h: H.t positive) (j': positive) (i: positive) :=
      let j := syracuse j' in
      if j <? i then (h, Ok)
      else
        match H.find j h with
        | Some i' => if i =? i' then (h, Loop i) else (h, Ok)
        | None    => k (H.add j i h) j i
        end.

  Definition for_i k (h: H.t positive) (i: positive) :=
    if H.mem i h || (i =? 1) then
      k (H.remove i h) (i + 1)
    else
      match Pos.iter while (fun h _ _ => (h, TimeOut i)) 1000 h i i with
      | (h, Ok) => k h (i + 1)
      | x       => x
      end.

  Definition syracuse_launch n :=
    Pos.iter for_i (fun h _ => (h, Ok)) n (H.empty positive) 1.

End FTest.

Module HTree := HashTableTree POS.
Module TestTree := Test HTree.

Module HBucket := HashTableBucket POS.
Module TestBucket := Test HBucket.

Time Compute snd (FTest.syracuse_launch 1000000%positive).
Time Compute snd (TestTree.syracuse_launch 1000000%positive).
Time Compute snd (TestBucket.syracuse_launch 1000000%positive).

