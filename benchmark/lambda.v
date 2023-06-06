Require Import hashtable dict module utils.
Require Import Nat ZArith Bool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import quicksort.

Open Scope uint63_scope.

Module Term <: Hash_type.
  Definition A := term.

  Fixpoint eq n m :=
    match n, m with
    | Ref i, Ref j => i =? j
    | Abs u, Abs v => eq u v
    | App u1 u2, App v1 v2 => if eq u1 v1 then eq u2 v2 else false
    | _, _ => false
    end.

  Lemma eqb_eq_refl:
    forall n m, reflect (n = m) (eq n m).
  Proof.
    induction n; destruct m; simpl; try now apply ReflectF.
    + case (i =? i0) eqn:H. apply eqb_spec in H. apply ReflectT. now rewrite H.
      apply ReflectF. intros [= <-]. now rewrite eqb_refl in H.
    + case (IHn m) as [<- | Hneq]. now apply ReflectT. apply ReflectF.
      now intros [= <-].
    + case (IHn1 m1) as [<- | H0]. case (IHn2 m2) as [<- | H1].
      now apply ReflectT. all:apply ReflectF; now intros [= <-].
  Qed.

  Definition eq_spec := eqb_eq_refl.

  Fixpoint hashi (t: term): int :=
    match t with
    | Ref i => i
    | Abs t => (19 * hashi t + 1)
    | App u v => (19 * (19 * hashi u + hashi v) + 2)
    end.

  Definition hashp (t: term): positive :=
    let hi := hashi t in
    match to_Z hi with
    | Z.pos p => p
    | _ => xH
    end.
End Term.

Module Test (H: HashTable Term).

  Record ht : Type := hash_tabs {
    (* lift_h : H.t term; *)
    (* subst_h : H.t term; *)
    t_nf : H.t term;
    t_hnf : H.t term;
  }.

  Definition memo_nf ht t nt :=
    hash_tabs (H.add (t_nf ht) t nt) (t_hnf ht).

  Definition memo_hnf ht t nt :=
    hash_tabs (t_nf ht) (H.add (t_hnf ht) t nt).

  Definition lift n :=
    let lift_rec :=
      fix lift_rec k t :=
        match t with
        | Ref i => if i <? k then t else Ref (n + i)
        | Abs t => Abs (lift_rec (k + 1) t)
        | App t u => App (lift_rec k t) (lift_rec k u)
        end
    in
    lift_rec 0.

  Definition subst w :=
    let subst_w :=
      fix subst_w n t :=
        match t with
        | Ref k =>
          if k =? n then lift n w
          else if k <? n then t
          else Ref (k - 1)
        | Abs t => Abs (subst_w (n + 1) t)
        | App t u => App (subst_w n t) (subst_w n u)
        end
    in
    subst_w 0.

  Fixpoint fuell_hnf n t (ht : ht) :=
    match H.find (t_hnf ht) t with
    | Some t => (ht, t)
    | None =>
        match n, t with
        | O, _ => (ht, t)
        | S _, Ref n => (ht, t)
        | S n, Abs t =>
            let (ht, v) := fuell_hnf n t ht in
            (memo_hnf ht t v, Abs v)
        | S n, App t u =>
            match fuell_hnf n t ht with
            | (ht, Abs w) =>
                let s := (subst u w) in
                let (ht, v) := fuell_hnf n s ht in
                (memo_hnf ht s v, v)
                (* fuell_hnf n (subst u w) ht *)
            | (ht, h) => (memo_hnf ht t h, App h u)
            end
        end
    end.

  Fixpoint fuell_nf n t (ht: ht) :=
    match H.find (t_nf ht) t with
    | Some t => (ht, t)
    | None =>
        match n, t with
        | O, _ => (ht, t)
        | S _, Ref n => (ht,t)
        | S n, Abs t =>
            let (ht, v) := fuell_nf n t ht in
            (memo_nf ht t (Abs v), Abs v)
        | S n, App t u =>
            match fuell_hnf n t ht with
            | (ht, Abs w) =>
                let s := (subst u w) in
                let (ht, v) := fuell_nf n s ht in
                (memo_nf ht s v, v)
            | (ht, h) =>
                let (ht1, v1) := fuell_nf n h ht in
                let ht2 := memo_nf ht1 h v1 in
                let (ht3, v2) := fuell_nf n u ht2 in
                (memo_nf ht u v2, App v1 v2)
            end
        end
    end.

  (* Definition hnf t := fuell_hnf 1000 t. *)
  Definition nf t  :=
    (fuell_nf 1000 t (hash_tabs (H.create 100) (H.create 100))).

  Definition nil := (*[c,n]n*) Abs (Abs (Ref 0)).
  Definition cons := (*[x,l][c,n](c x (l c n))*)
    Abs (Abs (Abs (Abs (
      App (App (Ref 1) (Ref 3))
          (App (App (Ref 2) (Ref 1)) (Ref 0)))))).

  Definition zero := Abs (Abs (Ref 0)).
  Definition succ :=
    Abs (Abs (Abs (
      App (Ref 1)
          (App (App (Ref 2) (Ref 1)) (Ref 0))))).

  Definition church n :=
    fold_int (fun _ t => snd (nf (App succ t)) ) n zero.

  Fixpoint list l :=
    match l with
    | x :: l =>
        let cx := church x in
        let ll := list l in
        (*[c,n](c x (l c n))*)
        Abs (Abs (App (App (Ref 1) cx)
          (App (App ll (Ref 1)) (Ref 0))))
    | [] => nil
    end.

  (* Back *)

  Fixpoint eval_iter {T: Type} (iter: option T -> option T) init t :=
    match t with
    | Ref i => if i =? 0 then init else None
    | App (Ref i) u =>
        if i =? 1
        then iter (eval_iter iter init u)
        else None
    | _ => None
    end.

  Definition compute_nat t :=
    match t with
    | Abs (Abs t) =>
        eval_iter
          (fun i =>
            match i with
            | Some i => Some (i+1)
            | None => None end)
          (Some 0) t
    | _ => None
    end.

  Definition eval_list_of_nats t :=
    match t with
    | Abs (Abs t) =>
        let lrec :=
          fix lrec t :=
            match t with
            | Ref i => if i =? 0 then Some [] else None
            | App (App (Ref i) x) l =>
                if i =? 1 then
                  match compute_nat x, lrec l with
                  | Some x, Some ll => Some (x :: ll)
                  | _, _ => None
                  end
                else None
            | _ => None
            end
        in
        lrec t
    | _ => None
    end.

  Definition normal_nat n := compute_nat (snd (nf n)).
  Definition normal_list l := 
    let (ht, t) := nf l in
    (ht, eval_list_of_nats t).

End Test.


(* bench *)
Module HTree := HashTableTree Term.
Module TestTree := Test HTree.

Module HBucket := HashTableBucket Term.
Module TestBucket := Test HBucket.

Definition l := TestBucket.list [0].
Time Compute TestTree.normal_list (App quicksort l).
Time Compute TestBucket.normal_list (App quicksort l).

