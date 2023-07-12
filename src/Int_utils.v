Require Import ZArith.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

(** Simple Facts on int *)

Lemma eqbPF_to_Z:
  forall x y, x =? y = false <-> to_Z x <> to_Z y.
Proof.
  intros x y.
  split.
  + intros H. case (eqbP x y) in H. discriminate. assumption.
  + intros H. case (eqbP x y). intros H'. contradiction H.
    easy.
Qed.

Lemma eqbPT_to_Z:
  forall x y, x =? y = true <-> to_Z x = to_Z y.
Proof.
  intros x y.
  split.
  + intros H. case (eqbP x y) in H; try discriminate. assumption.
  + intros H. case (eqbP x y); try easy.
Qed.

Lemma add_neutral:
  forall (u: int), u + 0 = u.
Proof.
  intros u. rewrite <- of_to_Z at 1.
  rewrite add_spec. change (to_Z 0) with 0%Z.
  rewrite Z.add_0_r. rewrite Z.mod_small.
  apply of_to_Z.
  generalize (to_Z_bounded u). lia.
Qed.

(** Fold_int functions *)

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

Definition R x y := (y <? x) = true.

Definition fold_int' (T : Type) (f : int -> T -> T) (s e : int) (acc : T)
  (H : Acc R s) :=
(fix cont (i : int) (acc : T) (H : Acc R i) {struct H} : T :=
   let b := i <? e in
   (if b return ((i <? e) = b -> T)
    then
     fun Hb =>
     cont (i + 1) (f i acc)
       match H with
       | Acc_intro _ H => H (i + 1) (fold_int_aux i e Hb)
       end
    else fun _ => acc) (eq_refl b)) s acc H.

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
  fold_int' T f 0 e acc (Acc_intro_generator 22 acc_int 0).

(** Fold_int spec *)

Lemma suc_sub:
  forall n m,
  m < n ->
  (S (n - S m) = n - m)%nat.
Proof.
  intros n.
  induction n; intros m Hm.
  + contradiction (Nat.nlt_0_r m).
  + simpl. destruct m as [| m'] eqn:Hm'.
    now rewrite Nat.sub_0_r.
    rewrite IHn. easy.
    now apply Nat.succ_lt_mono.
Qed.

Lemma nat_rect_one:
  forall T f n x acc,
  to_Z x = Z.of_nat n ->
  nat_rect (fun _ : nat => T) (f x acc)
    (fun (n0 : nat) (acc0 : T) => f (of_pos (Pos.of_succ_nat (n + n0))) acc0) 0 =
  f (of_Z (Z.of_nat (n + 0)))
    (nat_rect (fun _ : nat => T) acc
      (fun (n0 : nat) (acc0 : T) => f (of_Z (Z.of_nat (n + n0))) acc0) 0).
Proof.
  intros T f n x acc Hxn.
  destruct n as [| n'].
  + simpl. simpl in Hxn. change 0%Z with (to_Z 0) in Hxn.
    assert (H: x = 0). now apply to_Z_inj.
    now rewrite H.
  + simpl. rewrite Nat.add_0_r.
    assert (H:of_pos (Pos.of_succ_nat n') = of_Z (Z.of_nat (S n'))).
    { destruct n'. easy. simpl. easy. }
    assert (H': x = of_Z (Z.of_nat (S n'))).
    { apply to_Z_inj. rewrite Hxn. rewrite of_Z_spec, Z.mod_small. easy.
      rewrite <- Hxn. apply to_Z_bounded. }
    rewrite H, H'. easy.
Qed.

Lemma fold_int_spec :
  forall T (f : int -> T -> T) e acc,
  fold_int f e acc =
  nat_rect (fun _ => T) acc
           (fun n acc => f (of_Z (Z.of_nat n)) acc)
           (Z.to_nat (to_Z e)).
Proof.
  intros T f e. unfold fold_int.
  rewrite <- (Nat.sub_0_r (Z.to_nat φ (e))).
  generalize (Acc_intro_generator 22 acc_int 0).
  change (fun (n : nat) (acc0 : T) => f (of_Z (Z.of_nat n)) acc0) with
    (fun (n : nat) (acc0 : T) => f (of_Z (Z.of_nat (0 + n))) acc0).
  cut (to_Z 0 = Z.of_nat 0). 2: easy.
  cut (Z.of_nat 0 <= to_Z e)%Z. 2: apply to_Z_bounded.
  generalize 0%nat.
  intros n He Hn a. revert a n Hn He.
  generalize 0. induction a using Acc_inv_dep.
  simpl. intros n Hn He acc. generalize (eq_refl (x <? e)).
  destruct (x <? e) at 2 3.
  + intros Hx. rewrite (H (x + 1) (fold_int_aux x e Hx) (S n)).
    replace (Z.to_nat (to_Z e) - n)%nat with (S (Z.to_nat (to_Z e) - S n)).
    clear -Hn. simpl. induction (Z.to_nat (to_Z e) - S n)%nat as [| n0 IHn0].
    now apply nat_rect_one.
    simpl. rewrite <- IHn0. f_equal. rewrite Nat.add_succ_r. simpl. easy.
    apply suc_sub. rewrite ltb_spec in Hx. rewrite Hn in Hx.
    rewrite Nat2Z.inj_lt, Z2Nat.id. exact Hx. apply to_Z_bounded.
    rewrite add_spec. rewrite Z.mod_small. rewrite inj_S. rewrite Hn. easy.
    rewrite ltb_spec in Hx. generalize (to_Z_bounded e). change (to_Z 1) with 1%Z.
    lia.
    rewrite ltb_spec in Hx. rewrite Hn in Hx. rewrite Nat2Z.inj_succ.
    now apply Z.le_succ_l.
  + case ltbP. easy. rewrite Hn. intros H' _.
    rewrite (proj2 (Nat.sub_0_le (Z.to_nat (to_Z e)) n)). easy.
    lia.
Qed.

