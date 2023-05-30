Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Open Scope uint63_scope.

Import ListNotations.

Section List.
  Variable A: Type.
  Variable B: Type.

  Fixpoint find_snd (f : A * B -> bool) (l :list (A * B)): option B :=
    match l with
    | nil     => None
    | x :: tl => if f x then Some (snd x) else find_snd f tl
    end.
End List.

Arguments find_snd : clear implicits.

Lemma add_neutral:
  forall (u: int), u + 0 = u.
Proof.
  intros u. rewrite <- of_to_Z at 1.
  rewrite add_spec. change (to_Z 0) with 0%Z.
  rewrite Z.add_0_r. rewrite Z.mod_small.
  apply of_to_Z.
  generalize (to_Z_bounded u). lia.
Qed.

Lemma of_Z_add:
  forall (u v: Z), of_Z (u + v)%Z = of_Z u + of_Z v.
Proof.
  induction u.
  (* simpl. intros v.  apply Z.add_0_l. Search (0 + _ = _)%Z. *)
Admitted.

Lemma fold_int_aux:
  forall (i e: int), i <? e = true-> i <? i + 1 = true.
Proof.
  intros i e H.
  apply ltb_spec. rewrite add_spec.
  rewrite Z.mod_small. apply Z.lt_succ_diag_r.
  apply ltb_spec in H.
  generalize (to_Z_bounded e) (to_Z_bounded i). change (to_Z 1) with 1%Z.
  lia.
Qed.


Definition fold_int' (T: Type) (f : int -> T -> T) 
                     (e: int) (acc: T) 
                     (H: Acc (fun x y => y <? x = true) 0 ): T.
Proof.
  revert acc H.
  generalize 0.
  fix cont 3.
  intros i acc H.
  case (i <? e) eqn:Hlt. 2: exact acc.
  apply (cont (i+1) (f i acc)).
  case H. intros H0. apply H0. apply (fold_int_aux _ _ Hlt).
Defined.

Print fold_int'.

Lemma acc_int:
  forall x, Acc (fun x y => y <? x = true) x.
Proof.
  assert (H: forall y, of_Z (wB - 1 - (wB - 1 - to_Z y)) = y).
  { intros y.
    rewrite <- (of_to_Z y) at 2.
    apply f_equal. ring. }
  intros x.
  rewrite <- H.
  apply (Z_lt_induction 
          (fun x => to_Z (of_Z x) = x -> 
          Acc (fun x y : int => (y <? x) = true) (of_Z (wB - 1 - x)))).
  clear x.
  intros x IHn Hpos.
  apply Acc_intro.
  intros y Heq.
  rewrite <- H.
  apply IHn. split.
  generalize (to_Z_bounded y). lia.
  apply ltb_spec in Heq.
  rewrite of_Z_spec, Z.mod_small in Heq. lia.
  rewrite <- Hpos.
  generalize (to_Z_bounded (of_Z x)). lia.
  rewrite of_Z_spec. apply Z.mod_small.
  generalize (to_Z_bounded y). lia.
  generalize (to_Z_bounded x). lia.
  rewrite of_Z_spec. apply Z.mod_small.
  generalize (to_Z_bounded x). lia.
Qed.

Definition fold_int {T: Type} (f : int -> T -> T) (e: int) (acc: T) :=
  fold_int' T f e acc (Acc_intro_generator 22 acc_int 0).

Lemma fold_int_spec :
  forall T (f : int -> T -> T) e acc,
  fold_int f e acc =
  nat_rect (fun _ => T) acc 
           (fun n acc => f (of_Z (Z.of_nat n)) acc)
           (Z.to_nat (to_Z e)).
Proof.
  intros T f e.
  pattern e at 1.
  elim of_to_Z.
  generalize (proj2 (to_Z_bounded e)).
  pattern (to_Z e) at 1 2.
  elim Z2Nat.id. 2: apply to_Z_bounded.
  induction (Z.to_nat (to_Z e)). easy.
  rewrite Nat2Z.inj_succ.
  unfold Z.succ. intros Hs.
  rewrite of_Z_add. change (of_Z 1) with 1. simpl.
  unfold fold_int, fold_int'. generalize (Acc_intro_generator 22 acc_int 0).
  


  case (i <? of_Z (Z.of_nat n) + 1).
Admitted.

Definition v := fold_int (fun n acc => n :: acc ) 3 [].

Compute v.

Definition v' := nat_rect _ [] (fun n acc => of_Z (Z.of_nat n) :: acc ) 3.

Compute v'.

