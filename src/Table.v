Require Import Coq.Array.PArray.
Require Import Coq.Init.Nat PeanoNat ZArith.
Require Import Bool.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.ssr.ssrbool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import int_utils.
Import ListNotations.

Open Scope uint63_scope.

(** hashtable implantation with PArray *)

Section Hashtable.
  Context {A B: Set}.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable hash: A -> int.

  Inductive bucket : Set :=
    | Empty : bucket
    | Cons : int -> A -> B -> bucket -> bucket.

  Definition table := PArray.array bucket.

  Record t : Set := hash_tab {
    size : int;
    hashtab : table;
  }.

  (** ** Hashtable functions *)

  Definition length t : int :=
    PArray.length (hashtab t).

  Definition create (size: int) : t :=
    let h := make size Empty in
    hash_tab 0 h.

  Definition key_index (s: int) (k: int) : int :=
    k mod s.

  Definition get_bucket (h: t) (k: int) : bucket :=
    if length h =? 0 then Empty
    else (hashtab h).[key_index (length h) k].

  Definition resize_heurisitic (h: t) : bool :=
    (length h << 1 <=? size h) && negb (length h =? PArray.max_length).

  Opaque resize_heurisitic.

  Fixpoint fold_right {T:Type} f (a: T) b :=
    match b with
    | Empty => a
    | Cons h k v b' => f h k v (fold_right f a b')
    end.

  Definition rehash_bucket (nt lt: table) (ns ls i: int) : table :=
    fold_right (fun h k v a =>
      if i =? key_index ls h then
        let h_b := key_index ns h in
        a.[h_b <- Cons h k v a.[h_b]]
      else a)
    nt lt.[i].

  Definition copy_tab (ht: t) (i: int) : t :=
    let last_size := length ht in
    let new_size := last_size * 2 in
    let a := make new_size Empty in
    let new_tab :=
      fold_int (fun i a =>
        rehash_bucket a (hashtab ht) (PArray.length a) (length ht) i)
      i a
    in
    hash_tab (size ht) new_tab.

  Definition resize (ht: t): t :=
    if length ht =? 0 then
      hash_tab 0 (make 16 Empty)
    else if resize_heurisitic ht then
      copy_tab ht (length ht)
    else ht.

  Fixpoint bucket_remove (b: bucket) (hash: int) (key: A) :=
    match b with
    | Empty  => (false, Empty)
    | Cons hash' key' v b =>
        if if hash =? hash' then eq key key' else false
        then (true, b)
        else
          let new_bucket := bucket_remove b hash key in
          (fst new_bucket, Cons hash' key' v (snd new_bucket))
    end.

  Definition remove (h: t) (key: A) : t :=
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index (length h) hash in
    let b_remove := bucket_remove tab.[i] hash key in
    if fst b_remove
    then hash_tab (size h - 1) (tab.[i <- snd b_remove])
    else h.

  Definition add (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index (length h) hash in
    let new := Cons hash key v tab.[i] in
    hash_tab (size h + 1) tab.[i<-new].

  Definition replace (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index (length h) hash in
    let remove_result := bucket_remove tab.[i] hash key in
    let new_size := if fst remove_result then (size h) else (size h) + 1 in
    hash_tab new_size tab.[i <- Cons hash key v (snd remove_result)].

  Fixpoint find_rec (l: bucket) (h: int) (k: A): option B :=
    match l with
    | Empty => None
    | Cons h' k' v l' =>
        if if h =? h' then eq k k' else false
        then Some v
        else find_rec l' h k
    end.

  Definition find (h: t) (key: A) : option B :=
    let hash := hash key in
    let bucket := get_bucket h hash in
    find_rec bucket hash key.

  Fixpoint find_all_rec (l: bucket) (h: int) (k: A) (acc: list B): list B :=
    match l with
    | Empty => List.rev' acc
    | Cons h' k' v l' =>
        if if h =? h' then eq k k' else false
        then find_all_rec l' h k (v :: acc)
        else find_all_rec l' h k acc
    end.

  Definition mem (h: t) (key: A) : bool :=
    match find h key with
    | Some _ => true
    | None   => false
    end.

  Definition find_all (h: t) (key: A) : list B :=
    let hash := hash key in
    find_all_rec (get_bucket h hash) hash key [].

  Fixpoint elements_bucket l b i s :=
    match b with
    | Empty         => l
    | Cons h k v b' =>
        if key_index s h =? i
        then elements_bucket ((k, v) :: l) b' i s
        else elements_bucket l b' i s
    end.

  Definition elements h :=
    let s := length h in
    fold_int (fun i l => elements_bucket l (hashtab h).[i] i s) s [].

  Fixpoint fold_bucket {Acc: Type} b f i s (acc: Acc) :=
    match b with
    | Empty         => acc
    | Cons h k v b' =>
        if key_index s h =? i
        then fold_bucket b' f i s (f k v acc)
        else fold_bucket b' f i s acc
    end.

  Definition fold {Acc: Type} h f (acc: Acc) :=
    let length := length h in
    fold_int (fun i => fold_bucket (hashtab h).[i] f i length) length acc.

  (** ** Hashtables facts *)

  (** Eq *)
  Lemma eq_true:
    forall (k1 k2 : A), k1 = k2 -> eq k1 k2 = true.
  Proof.
    intros k1 k2 H.
    now case eq_spec.
  Qed.

  Lemma eq_false:
    forall (k1 k2 : A), k1 <> k2 -> eq k1 k2 = false.
  Proof.
    intros k1 k2 H.
    now case eq_spec.
  Qed.

  Lemma eq_refl:
    forall (k : A), eq k k = true.
  Proof.
    intros k.
    now case eq_spec.
  Qed.

  Lemma neq_sym:
    forall (k k' : A), k <> k' -> k' <> k.
  Proof.
    intros k k' H. intro nH.
    apply H. now apply eq_sym.
  Qed.

  (** find_all *)

  Fixpoint find_all_rec' (l: bucket) (h: int) (k: A) : list B :=
    match l with
    | Empty => []
    | Cons h' k' v l' =>
        if if h =? h' then eq k k' else false
        then v :: find_all_rec' l' h k
        else find_all_rec' l' h k
    end.

  Lemma find_all_rec_correct:
    forall (l: bucket) (h: int) (key: A) acc,
    find_all_rec l h key acc = rev acc ++ find_all_rec' l h key.
  Proof.
    intros l h k.
    induction l.
    + intros acc. simpl. apply rev_append_rev.
    + intros acc. simpl. case (eq k a) eqn:H.
      - case (h =? i).
        * rewrite IHl. simpl. rewrite <- app_assoc. easy.
        * simpl. apply IHl.
      - case (h =? i).
        * rewrite IHl. reflexivity.
        * apply IHl.
  Qed.

  (** resize *)

  Lemma rehash_bucket_length:
    forall (nt lt: table) i,
    PArray.length (rehash_bucket nt lt (PArray.length nt) (PArray.length lt) i)
    = PArray.length nt.
  Proof.
    intros nt lt i.
    unfold rehash_bucket.
    induction lt.[i]; simpl.
    + easy.
    + case (i =? key_index _ _); [rewrite length_set|]; apply IHb.
  Qed.

  Lemma copy_tab_lenght:
    forall (ht: t) (i: int),
    PArray.length (hashtab ht) =? 0 = false ->
    PArray.length (hashtab (copy_tab ht i)) =? 0 = false.
  Proof.
    intros ht i H.
    unfold copy_tab. simpl.
    rewrite fold_int_spec.
    induction (Z.to_nat (to_Z i)).
    + simpl. rewrite length_make.
      case (_ <=? _).
      - rewrite eqbPF_to_Z in *. change (to_Z 0) with 0%Z in *.
        rewrite mul_spec. change (to_Z 2) with 2%Z. rewrite Z.mod_small.
        apply Z.neq_mul_0. split. unfold length in H. exact H. easy.
        generalize (leb_length _ (hashtab ht)). rewrite leb_spec.
        generalize (to_Z_bounded (PArray.length (hashtab ht))). cbn. lia.
      - reflexivity.
    + simpl.
      rewrite rehash_bucket_length.
      apply IHn.
  Qed.

  Lemma length_resize_non_neg:
    forall (h: t),
    (length (resize h)) =? 0 = false.
  Proof.
    intros h. unfold resize.
    case (length h =? 0) eqn:H. now simpl.
    case (resize_heurisitic h).
    - unfold length. now rewrite copy_tab_lenght.
    - now unfold length in *.
  Qed.

  Lemma fold_right_length:
    forall nt lt i0 i b,
    (PArray.length nt =? 0) = false ->
    (i0 mod PArray.length nt <?
      PArray.length
       (fold_right
          (fun (h : int) (k : A) (v : B) (a0 : array bucket) =>
           if i =? key_index (length lt) h
           then
            a0.[key_index (PArray.length nt) h <-Cons h k v a0.[key_index (PArray.length nt) h]]
           else a0) nt b)) = true.
  Proof.
    intros nt lt i0 i b H.
    induction b. simpl. rewrite ltb_spec, mod_spec.
    apply Z.mod_pos_bound. generalize (to_Z_bounded (PArray.length nt)).
    case (eqbP (PArray.length nt) 0) as [| H'] in H; try discriminate.
    change (to_Z 0) with 0%Z in H'. lia.
    simpl. case (i =? _). 2: apply IHb.
    rewrite PArray.length_set. apply IHb.
  Qed.

  Lemma rehash_bucket_correct1:
    forall (nt: table) (lt: t) (k: A) (i s: int),
    length lt =? 0 = false ->
    PArray.length nt =? 0 = false ->
    i = key_index (length lt) (hash k) ->
    find_all (hash_tab s nt) k = [] ->
    find_all (hash_tab s (rehash_bucket nt (hashtab lt)
                            (PArray.length nt) (length lt) i)) k =
    find_all lt k.
  Proof.
    intros nt lt j i s Hlt Hnt H Hf.
    unfold find_all, get_bucket, length.
    simpl. rewrite rehash_bucket_length. rewrite Hnt.
    unfold length in Hlt. rewrite Hlt.
    unfold rehash_bucket. unfold length in *.
    rewrite <- H.
    induction (hashtab lt).[i].
    - simpl. unfold find_all in Hf.
      unfold get_bucket in Hf. unfold length in Hf. simpl in Hf.
      rewrite Hnt in Hf.
      rewrite Hf. now simpl.
    - simpl. case (i =? key_index (PArray.length (hashtab lt)) i0) eqn:Heq.
      + case (hash j =? i0) eqn:Hj.
        * rewrite eqb_spec in Hj. rewrite Hj.
          rewrite get_set_same. rewrite find_all_rec_correct.
          simpl. rewrite eqb_refl.
          case (eq j a); rewrite 2!find_all_rec_correct in IHb; simpl in IHb.
          rewrite find_all_rec_correct. apply f_equal.
          rewrite <- Hj. apply IHb.
          rewrite find_all_rec_correct. rewrite <- Hj. apply IHb.
          now apply fold_right_length.
        * simpl.
          case (key_index (PArray.length nt) i0 =? key_index (PArray.length nt) (hash j)) eqn:Hheq.
          **rewrite eqb_spec in Hheq. rewrite Hheq, get_set_same.
            rewrite 2!find_all_rec_correct. simpl. rewrite Hj. simpl.
            rewrite 2!find_all_rec_correct in IHb. simpl in IHb. apply IHb.
            now apply fold_right_length.
          **rewrite get_set_other. apply IHb. now rewrite eqb_false_spec in Hheq.
      + rewrite IHb. rewrite H in Heq.
        case (eqbP (key_index (PArray.length (hashtab lt)) (hash j))
                (key_index (PArray.length (hashtab lt)) i0)) as [|Heq']in Heq.
        discriminate.
        unfold key_index in Heq'. rewrite 2!mod_spec in Heq'.
        (* assert (to_Z (hash j) <> to_Z i0). by (intros H'; now rewrite H' in Heq'). *)
        case (eqb (hash j) i0) eqn:Hji0. contradiction Heq'.
        apply eqb_spec in Hji0. now rewrite Hji0.
        easy.
  Qed.

  Lemma rehash_bucket_correct2:
    forall (nt: table) (lt: t) (k: A) (i s: int),
    length lt =? 0 = false ->
    PArray.length nt =? 0 = false ->
    i <> key_index (length lt) (hash k) ->
    (to_Z (length lt) <= to_Z (PArray.length nt))%Z ->
    find_all (hash_tab s (rehash_bucket nt (hashtab lt)
                            (PArray.length nt) (length lt) i)) k =
    find_all (hash_tab s nt) k.
  Proof.
    intros nt lt j i s Hlt Hnt H Hf.
    unfold find_all, get_bucket, length.
    simpl. rewrite rehash_bucket_length. rewrite Hnt.
    unfold rehash_bucket. unfold length in *.
    induction (hashtab lt).[i]. now simpl.
    simpl. case (i =? key_index _ i0) eqn:Heq.
    2: apply IHb.
    case (key_index (PArray.length nt) i0=? key_index (PArray.length nt) (hash j)) eqn:Hm.
    + rewrite eqb_spec in Hm. rewrite Hm. rewrite get_set_same.
      rewrite find_all_rec_correct. simpl.
      assert (Hd: hash j <> i0).
      { rewrite eqb_spec in Heq. rewrite Heq in H.
        intros Hd. rewrite Hd in H. now apply H. }
      rewrite <- eqb_false_spec in Hd. rewrite Hd. simpl.
      rewrite find_all_rec_correct in IHb. simpl in IHb. exact IHb.
      now apply fold_right_length.
    + rewrite get_set_other. exact IHb. now rewrite eqb_false_spec in Hm.
  Qed.

  Lemma length_rect_non_neg:
    forall ht n,
    length ht =? 0 = false ->
    PArray.length
      (nat_rect (fun _ : nat => table) (make (length ht * 2) Empty)
        (fun (n0 : nat) (acc : table) =>
          rehash_bucket acc (hashtab ht) (PArray.length acc)
          (length ht) (of_Z (Z.of_nat n0))) n) =? 0 = false.
  Proof.
    intros ht n H.
    induction n.
    + simpl. rewrite length_make.
      case (length ht * 2 <=? max_length) eqn:H'.
      rewrite eqbPF_to_Z in *. change (to_Z 0) with 0%Z in *.
      rewrite mul_spec. change (to_Z 2) with 2%Z.
      rewrite Z.mod_small. lia.
      generalize (leb_length _ (hashtab ht)). rewrite leb_spec.
      generalize (to_Z_bounded (length ht)). cbn. lia.
      rewrite eqbPF_to_Z. cbn. easy.
    + simpl. rewrite rehash_bucket_length. apply IHn.
  Qed.

  Lemma length_rect_min:
    forall ht n,
    length ht <=?
      PArray.length
        (nat_rect (fun _ : nat => table) (make (length ht * 2) Empty)
          (fun (n0 : nat) (acc : table) =>
            rehash_bucket acc (hashtab ht) (PArray.length acc)
            (length ht) (of_Z (Z.of_nat n0))) n) = true.
  Proof.
    induction n.
    + simpl. rewrite length_make.
      case (length ht * 2 <=? max_length) eqn:H.
      generalize (leb_length _ (hashtab ht)).
      rewrite 2!leb_spec, mul_spec. change (to_Z 2) with 2%Z.
      rewrite Z.mod_small. generalize (to_Z_bounded (length ht)). lia.
      split. generalize (to_Z_bounded (length ht)). lia.
      apply Z.le_lt_trans with (m:= ((to_Z max_length) * 2)%Z).
      generalize (leb_length _ (hashtab ht)). rewrite leb_spec.
      unfold length. lia. cbn. lia.
      unfold length. apply leb_length.
    + simpl. rewrite rehash_bucket_length. apply IHn.
  Qed.

  Lemma copy_tab_correct:
    forall (ht: t) (k: A) (i: int),
      length ht =? 0 = false ->
      key_index (length ht) (hash k) <? i = true ->
      find_all (copy_tab ht i) k = find_all ht k.
  Proof.
    intros ht k i H. unfold length. rewrite ltb_spec. rewrite Z2Nat.inj_lt.
    2: generalize (to_Z_bounded (key_index (PArray.length (hashtab ht)) (hash k))); lia.
    2: generalize (to_Z_bounded i); lia.
    unfold copy_tab. rewrite fold_int_spec.
    generalize (to_Z_bounded i). intros Hb. destruct Hb as [_ HM].
    rewrite Z2Nat.inj_lt in HM. 3: cbn; lia. 2: generalize (to_Z_bounded i); lia.
    induction (Z.to_nat (to_Z i)).
    + intros. exfalso. easy.
    + case (Z.to_nat φ (key_index (PArray.length (hashtab ht)) (hash k)) <? n)%nat eqn:Hn.
      - simpl. intros _. rewrite rehash_bucket_correct2. apply IHn.
        lia. rewrite Nat.ltb_lt in Hn. exact Hn. exact H.
        apply length_rect_non_neg. assumption.
        rewrite <- eqb_false_spec, eqbPF_to_Z.
        rewrite Nat.ltb_lt in Hn. rewrite Nat2Z.inj_lt, Z2Nat.id in Hn.
        2: apply to_Z_bounded.
        rewrite of_Z_spec, Z.mod_small. 2: lia.
        unfold length. lia.
        rewrite <- leb_spec. apply length_rect_min.
      - simpl. intro H0. apply rehash_bucket_correct1. exact H.
        apply length_rect_non_neg. assumption.
        rewrite <- eqb_spec, eqbPT_to_Z, of_Z_spec, Z.mod_small.
        rewrite Nat.ltb_ge, Nat2Z.inj_le, Z2Nat.id in Hn.
        2: apply to_Z_bounded.
        unfold length. lia. lia.
        clear IHn H0. rewrite Nat.ltb_ge in Hn.
        induction n.
        * simpl. unfold find_all, get_bucket. simpl.
          case (length _ =? 0). now simpl.
          rewrite get_make. now simpl.
        * simpl. rewrite rehash_bucket_correct2. apply IHn.
          lia. lia. assumption. now rewrite length_rect_non_neg.
          rewrite <- eqb_false_spec, eqbPF_to_Z.
          rewrite of_Z_spec, Z.mod_small. 2: lia.
          rewrite Nat.le_succ_l, Nat2Z.inj_lt, Z2Nat.id in Hn.
          unfold length. lia. apply to_Z_bounded.
          now rewrite <- leb_spec, length_rect_min.
  Qed.

  Lemma find_all_resize:
    forall (h: t) (k: A),
    find_all (resize h) k = find_all h k.
  Proof.
    intros h k.
    case (PArray.length (hashtab h) =? 0) eqn:Heqb.
    - unfold resize, find_all, get_bucket.
      unfold length. rewrite Heqb.
      set (x:=make 16 Empty). simpl. unfold x.
      now rewrite get_make.
    - unfold resize, length. rewrite Heqb.
      case resize_heurisitic. 2: reflexivity.
      apply copy_tab_correct.
      unfold length. exact Heqb.
      unfold key_index.
      rewrite ltb_spec, mod_spec.
      apply Z.mod_pos_bound.
      generalize (to_Z_bounded (PArray.length (hashtab h))).
      destruct (eqbP (PArray.length (hashtab h)) 0). discriminate.
      rewrite to_Z_0 in n. lia.
  Qed.

  (** empty *)

  Theorem hempty:
    forall (k: A) (size: int), find (create size) k = None.
  Proof.
    intros k i. unfold create, find, get_bucket, length. simpl.
    rewrite length_make.
    case eqb. now simpl. now rewrite get_make.
  Qed.

  (** key_index *)

  Lemma key_index_max:
    forall (h: t) (k: int),
    (length h) =? 0 = false ->
    (to_Z (key_index (length h) k) < to_Z (PArray.length (hashtab h)))%Z.
  Proof.
    intros h k H.
    unfold key_index, length. rewrite mod_spec.
    apply Z.mod_pos_bound.
    generalize (to_Z_bounded (PArray.length (hashtab h))).
    rewrite eqbPF_to_Z in H. change (to_Z 0) with 0%Z in H.
    intros H0. apply Z.le_neq. split. apply H0.
    unfold length in H. lia.
  Qed.

  (** add *)

  Theorem find_add_same:
    forall (k: A) (v: B) (h: t),
    find_all (add h k v) k = v :: (find_all h k).
  Proof.
    intros k v h. rewrite <- (find_all_resize h).
    unfold find_all.
    rewrite 2!find_all_rec_correct.
    unfold get_bucket.
    rewrite 2!eqb_false_complete.
    replace (length (add h k v)) with (length (resize h)).
    unfold add; simpl. rewrite get_set_same.
    simpl. rewrite eqb_refl. rewrite eq_refl. easy.
    rewrite ltb_spec. apply key_index_max, length_resize_non_neg.
    unfold add; simpl. apply eq_sym, length_set.
    2:unfold add, length; simpl; rewrite length_set.
    all:rewrite <- eqb_false_spec; apply length_resize_non_neg.
  Qed.

  Theorem find_add_other:
    forall (k k': A) (v: B) (h: t),
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof.
    intros k k' v h Hdiff.
    assert (find_all (resize h) k' = find_all h k'). apply find_all_resize.
    unfold add, find_all, get_bucket, length in *. simpl.
    rewrite length_set in *. fold (length (resize h)) in *.
    rewrite length_resize_non_neg, find_all_rec_correct in *. simpl in *.
    case (key_index (length (resize h)) (hash k) =? key_index (length (resize h)) (hash k')) eqn:Heq.
    + rewrite eqb_spec in Heq. rewrite <- Heq, get_set_same in *.
      simpl. rewrite eq_false. 2:exact Hdiff.
      replace (if hash k' =? hash k then false else false) with false by now case (hash k' =? hash k).
      rewrite H. reflexivity.
      apply ltb_spec, key_index_max, length_resize_non_neg.
    + rewrite eqb_false_spec in Heq. rewrite get_set_other. 2:exact Heq.
      apply H.
  Qed.

  (** find *)

  Theorem find_spec:
    forall ht key,
    find ht key = List.hd_error (find_all ht key).
  Proof.
    intros ht key.
    unfold find_all, find. unfold get_bucket.
    case (length ht =? 0). reflexivity.
    induction (hashtab ht).[key_index (length ht) (hash key)]. reflexivity.
    simpl. case (if hash key =? i then eq key a else false).
    rewrite find_all_rec_correct. reflexivity.
    apply IHb.
  Qed.

  (** remove *)

  Lemma bucket_remove_same:
    forall (b: bucket) (k: A),
    let h := hash k in
    (fst (bucket_remove b h k) = false -> snd (bucket_remove b h k) = b) /\
    find_all_rec (snd (bucket_remove b h k)) h k []  =
    List.tl (find_all_rec b h k []).
  Proof.
    induction b; intros k h. easy. simpl.
    case (if h =? i then eq k a else false) eqn:Hc.
    + destruct (h =? i); try easy.
      rewrite 2!find_all_rec_correct. easy.
    + simpl. rewrite Hc. split.
      - intros Hbr. f_equal. now apply IHb.
      - apply IHb.
    Qed.

  Lemma bucket_remove_other:
    forall (b: bucket) (k k': A),
    let h := hash k in
    let h' := hash k' in
    k' <> k ->
    find_all_rec (snd (bucket_remove b h k)) h' k' []  =
    find_all_rec b h' k' [].
  Proof.
    induction b; intros k k' h h' Hk. easy. simpl.
    case (if h =? i then eq k a else false) eqn:Hc; simpl.
    + assert ((if h' =? i then eq k' a else false) = false).
      { case (h' =? i). 2:easy. apply eq_false.
        assert (Hkb: eq k a = true). case (h =? i) in Hc; easy.
        case (eq_spec k a) in Hkb; try discriminate.
        rewrite <- e. apply Hk. }
      rewrite H. reflexivity.
    + case (if h' =? i then eq k' a else false).
      - rewrite 2!find_all_rec_correct. f_equal.
        rewrite <- app_nil_l at 1. rewrite <- app_nil_l.
        assert (H:@rev (list B) [] = []). reflexivity.
        change [] with (@rev B []).
        rewrite <- 2!find_all_rec_correct. apply IHb. exact Hk.
      - apply IHb. exact Hk.
    Qed.

  Theorem remove_same:
    forall (ht: t) (k: A),
    find_all (remove ht k) k =
    List.tl (find_all ht k).
  Proof.
    intros ht k. unfold remove, find_all.
    generalize (bucket_remove_same (hashtab ht).[key_index (length ht) (hash k)] k).
    simpl.
    case (bucket_remove (hashtab ht).[key_index (length ht) (hash k)] (hash k) k).
    simpl. intros [|] l [H1 H2]. unfold get_bucket, length. simpl.
    rewrite length_set. case (PArray.length (hashtab ht) =? 0) eqn:Heq.
    reflexivity.
    simpl. rewrite get_set_same.
    apply H2. apply ltb_spec, key_index_max, Heq.
    unfold get_bucket. case (length ht =? 0). reflexivity.
    rewrite <- H1. rewrite <- H1 in H2. exact H2. all:easy.
  Qed.

  Theorem remove_other:
    forall (ht: t) (k: A) (k': A),
    k' <> k ->
    find_all (remove ht k) k' = find_all ht k'.
  Proof.
    intros ht k k1 Hk. unfold remove, find_all.
    simpl.
    case (fst (bucket_remove (hashtab ht).[key_index (length ht) (hash k)] (hash k) k)).
    simpl. 2:reflexivity.
    unfold get_bucket, length. simpl. rewrite length_set.
    case (PArray.length (hashtab ht) =? 0) eqn:Hl. reflexivity.
    case (key_index (PArray.length (hashtab ht)) (hash k) =?
          key_index (PArray.length (hashtab ht)) (hash k1)) eqn:Heq.
    apply eqb_spec in Heq. rewrite Heq. rewrite get_set_same.
    rewrite bucket_remove_other. reflexivity. exact Hk.
     apply ltb_spec, key_index_max, Hl.
    rewrite get_set_other. reflexivity.
    rewrite eqb_false_spec in Heq. exact Heq.
  Qed.

  (** replace *)

  Theorem replace_same:
    forall ht key v,
    find_all (replace ht key v) key = v :: (List.tl (find_all ht key)).
  Proof.
    intros ht key v. rewrite <- (find_all_resize ht).
    unfold find_all. rewrite 2!find_all_rec_correct.
    unfold get_bucket. rewrite 2!eqb_false_complete. simpl.
    assert (Heq: length (resize ht) = length (replace ht key v)).
    { unfold length, replace. simpl. now rewrite length_set. }
    rewrite Heq, get_set_same. simpl. rewrite eq_refl, eqb_refl. f_equal.
    generalize (bucket_remove_same
        (hashtab (resize ht)).[key_index (length (replace ht key v)) (hash key)] key).
    simpl. rewrite 2!find_all_rec_correct. simpl. now intros [_ ->].
    rewrite <- Heq.
    apply ltb_spec, key_index_max, length_resize_non_neg.
    2:unfold length, resize, replace; simpl; rewrite length_set.
    all:rewrite <- eqb_false_spec; apply length_resize_non_neg.
  Qed.

  Theorem replace_other:
    forall ht k1 k2 v,
    k1 <> k2 ->
    find_all (replace ht k1 v) k2 = find_all ht k2.
  Proof.
    intros ht k1 k2 v Hk.
    assert (H: find_all (resize ht) k2 = find_all ht k2) by apply find_all_resize.
    assert (Hl: PArray.length (hashtab (resize ht)) =? 0 = false).
    { assert (Hl: (length (resize ht) =? 0) = false)
      by apply length_resize_non_neg. easy. }
    unfold replace, find_all, get_bucket, length. simpl.
    rewrite length_set, Hl.
    case (key_index (PArray.length (hashtab (resize ht))) (hash k1) =?
          key_index (PArray.length (hashtab (resize ht))) (hash k2)) eqn:Heq.
    + rewrite eqb_spec in Heq. rewrite Heq. rewrite get_set_same. simpl.
      replace (if hash k2 =? hash k1 then eq k2 k1 else false) with false.
      rewrite <- Heq. rewrite bucket_remove_other. unfold find_all, get_bucket in H.
      rewrite length_resize_non_neg in H. rewrite Heq. apply H. now apply neq_sym.
      case (hash k2 =? hash k1). apply eq_sym, eq_false. now contradict Hk. easy.
      apply ltb_spec, key_index_max, Hl.
    + rewrite get_set_other. unfold find_all, get_bucket in H.
      rewrite length_resize_non_neg in H. apply H. rewrite eqb_false_spec in Heq.
      apply Heq.
  Qed.

  (** elements *)

  (* Fixpoint elements_bucket'' b := *)
  (*   match b with *)
  (*   | []            => [] *)
  (*   | C _ k v :: b' => (k, v) :: elements_bucket'' b' *)
  (*   end. *)
  (**)
  (* Definition elements_bucket' l b := *)
  (*   List.rev_append (elements_bucket'' b) l. *)
  (**)
  (* Lemma elements_bucket_rec: *)
  (*   forall b l, *)
  (*   elements_bucket l b = elements_bucket' l b. *)
  (* Proof. *)
  (*   induction b. easy. *)
  (*   unfold elements_bucket' in *. simpl. intros l. *)
  (*   destruct a as [_ k v]. now rewrite IHb. *)
  (* Qed. *)
  (**)
  (* Definition elements_to_findall (l : list (A * B)) key : list B := *)
  (*   List.map snd (List.filter (fun v => eq (fst v) key) l). *)
  (**)
  (* Lemma elements_to_findall_in: *)
  (*   forall l key v, *)
  (*   List.In v (elements_to_findall l key) -> *)
  (*   List.In (key, v) l. *)
  (* Proof. *)
  (*   induction l; intros key v; simpl. easy. *)
  (*   unfold elements_to_findall. simpl. *)
  (*   case (eq (fst a)) eqn:Heq. *)
  (*   + simpl. intros [Hs | H]. *)
  (*     - left. rewrite surjective_pairing at 1. *)
  (*       rewrite Hs. case (eq_spec (fst a) key) in Heq; try discriminate. *)
  (*       now rewrite e. *)
  (*     - right. apply IHl. now unfold elements_to_findall. *)
  (*   + intros H. right. apply IHl. now unfold elements_to_findall. *)
  (* Qed. *)
  (**)
  (* Lemma elements_to_findall_in_elements_bucket: *)
  (*   forall b l key v, *)
  (*   List.In v (elements_to_findall l key) -> *)
  (*   List.In (key, v) (elements_bucket l b). *)
  (* Proof. *)
  (*   induction b; intros l key v; simpl. exact (elements_to_findall_in _ _ _). *)
  (*   destruct a as [_ k v0]. intros H. apply IHb. *)
  (*   unfold elements_to_findall in *. simpl. *)
  (*   case eq. simpl. now right. easy. *)
  (* Qed. *)
  (**)
  (* Lemma find_all_rec_in_empty: *)
  (*   forall b l key v, *)
  (*   List.In v (find_all_rec b (hash key) key []) -> *)
  (*   List.In v (find_all_rec b (hash key) key l). *)
  (* Proof. *)
  (*   intros *. rewrite 2!find_all_rec_correct. simpl. *)
  (*   intros H. apply List.in_or_app. now right. *)
  (* Qed. *)
  (**)
  (* Lemma case_find_all_rec: *)
  (*   forall b l key v, *)
  (*   List.In v (find_all_rec b (hash key) key l) -> *)
  (*   List.In v l \/ List.In v (find_all_rec b (hash key) key []). *)
  (* Proof. *)
  (*   intros *. rewrite 2!find_all_rec_correct. simpl. *)
  (*   intros H. apply List.in_app_or in H as []. *)
  (*   left. now apply List.in_rev. now right. *)
  (* Qed. *)
  (**)
  (* Lemma elements_bucket_correct: *)
  (*   forall b l_elt key v, *)
  (*   List.In (key, v) l_elt \/ List.In (key, v) (elements_bucket [] b) -> *)
  (*   List.In (key, v) (elements_bucket l_elt b). *)
  (* Proof. *)
  (*   induction b. *)
  (*   + simpl. intros l k v [H|]; easy. *)
  (*   + simpl. destruct a as [_ k' v']. *)
  (*     intros l k v [Hl|He]. *)
  (*     - apply IHb. left. simpl. now right. *)
  (*     - apply IHb. rewrite elements_bucket_rec in *. *)
  (*       unfold elements_bucket' in *. rewrite rev_append_rev in *. *)
  (*       apply in_app_or in He as [|]. *)
  (*       * right. now rewrite app_nil_r. *)
  (*       * simpl in H. destruct H as [|]; try contradiction. *)
  (*         left. simpl. now left. *)
  (* Qed. *)
  (**)
  (* Lemma length_nat: *)
  (*   forall h l, *)
  (*   length h = l <-> Z.to_nat (to_Z (length h)) = Z.to_nat (to_Z l). *)
  (* Proof. *)
  (*   intros h l. split. *)
  (*   + intros H. f_equal. now f_equal. *)
  (*   + intros H. apply Z2Nat.inj in H. *)
  (*     now apply to_Z_inj in H. *)
  (*     generalize (to_Z_bounded (length h)). *)
  (*     2: generalize (to_Z_bounded l). all:lia. *)
  (* Qed. *)
  (**)
  (* (* Inductive count {T: Type} (v: T) : list T -> nat -> Prop := *) *)
  (* (*   | Count_nil : count nil 0%nat *) *)
  (**)
  (* Theorem elements_spec: *)
  (*   forall h k v, *)
  (*   List.count_occ v (find_all h k) = List.count_occ (k, v) (elements h). *)
  (* Proof. *)
  (*   intros h k v. unfold elements, find_all, get_bucket. *)
  (*   case (length h =? 0) eqn:Hl. easy. *)
  (*   rewrite eqb_false_spec, length_nat in Hl. simpl in Hl. *)
  (*   rewrite fold_int_spec. *)
  (*   induction (Z.to_nat (to_Z (length h))). *)
  (*   + contradiction Hl. easy. *)
  (*   + simpl. case ((n =? 0)%nat) eqn:Hn. *)
  (*     - rewrite Nat.eqb_eq in Hn. rewrite Hn. simpl. *)
  (*        *)
  (*       admit. *)
  (*     -  *)

  (** fold *)


  Lemma fold_correct:
    forall T h f (acc: T),
    fold h f acc =
    List.fold_right (fun v acc => f (fst v) (snd v) acc) acc (elements h).
  Proof.
    unfold fold, elements. intros T h f acc. rewrite 2!fold_int_spec.
    revert acc. induction (Z.to_nat φ (length h)). reflexivity.
    intros acc. simpl. rewrite IHn. set (nr:= nat_rect _ _ _ _).
    set (F:= fun _ => _). clear. generalize nr. clear nr.
    induction ((hashtab h).[of_Z (Z.of_nat n)]). reflexivity.
    intros nr. simpl.
    change (f a b (List.fold_right F acc nr)) with
           (List.fold_right F acc ((a, b) :: nr)).
    rewrite IHb. case (key_index (length h) i =? of_Z (Z.of_nat n)).
    + reflexivity.
    + apply IHb.
  Qed.

End Hashtable.

