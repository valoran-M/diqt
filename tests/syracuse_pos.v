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
    snd (Pos.iter for_i (fun h _ => (h, Ok)) n (H.create positive 16) 1).

End Test.

Module FPTest.
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
    snd (Pos.iter for_i (fun h _ => (h, Ok)) n (H.empty positive) 1).

End FPTest.

Module HTree := HashTableTree POS.
Module PTestTree := Test HTree.

Module HBucket := HashTableBucket POS.
Module PTestBucket := Test HBucket.

Time Compute FPTest.syracuse_launch 100000.

(*
   +-------------+--------+--------+--------+----------+----------+
   | syracuse n  | n=100  | n=1000 | n=10000| n=100000 | n=1000000|
   +-------------+--------+--------+--------+----------+----------+
   | FMap Pos    | 0.002s | 0.021s | 0.202s | 1.5s     | 16.969s  |
   +-------------+--------+--------+--------+----------+----------+
   | PRadix Tree | 0.003s | 0.035s | 0.158s | 1.794s   | 19.57s   |
   +-------------+--------+--------+--------+----------+----------+
   | PBucket     | 0.003s | 0.023s | 0.191s | 1.747s   | 18.251s  |
   +-------------+--------+--------+--------+----------+----------+
*)

