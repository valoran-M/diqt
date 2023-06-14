Require Import Coq.Array.PArray.
Require Import Coq.Init.Nat PeanoNat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import utils Coq.ssr.ssrbool.
Import ListNotations.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Open Scope uint63_scope.

Section Hashtable.
  Context {A B: Set}.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable hash: A -> int.

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

  Inductive bucket_e : Set :=
    | C : int -> A -> B  -> bucket_e.

  Definition bucket := list (bucket_e).
  Definition table := PArray.array bucket.
  
  Record t : Set := hash_tab { 
    size : int;
    hashtab : table; 
  }.

  Definition length t : int :=
    PArray.length (hashtab t).

  Fixpoint power_2_above' (n: nat) (x p: int) {struct n} : int :=
    match n with
    | O    => p
    | S n' => 
        if (p <? x) then 
          power_2_above' n' x (p * 2)
        else 
          p
    end.
  
  (* 2**22 - 1 = max_length *)
  Definition power_2_above := power_2_above' 22%nat.

  Definition create (initial_size: int) : t :=
    let size := power_2_above initial_size 16 in
    let h := make size [] in
    hash_tab 0 h.

  Definition key_index (h: t) (k: int) : int :=
    k mod length h.

  Lemma key_index_max:
    forall (h: t) (k: int),
    (length h) =? 0 = false ->
    (to_Z (key_index h k) < to_Z (PArray.length (hashtab h)))%Z.
  Proof.
    intros h k H.
    unfold key_index, length. rewrite mod_spec.
    apply Z.mod_pos_bound.
    generalize (to_Z_bounded (PArray.length (hashtab h))).
    rewrite eqbP_false_to_Z in H. change (to_Z 0) with 0%Z in H.
    intros H0. apply Z.le_neq. split. apply H0.
    unfold length in H. lia.
  Qed.

  Definition get_bucket (h: t) (k: int) : bucket :=
    if length h =? 0 then []
    else (hashtab h).[key_index h k].

  Definition resize_heurisitic (h: t) : bool :=
    (length h << 1 <=? size h) && negb (length h =? PArray.max_length).
  Opaque resize_heurisitic.

  Definition replace_bucket (nt lt: table) (ns ls i: int) : table :=
    fold_right (fun (e: bucket_e) a =>
      let (h, k, v) := e in
      if i =? h mod ls then
        a.[h mod ns <- e :: a.[h mod ns]]
      else a)
    nt lt.[i].

  Definition copy_tab (ht: t) (i: int) : t :=
    let last_size := length ht in
    let new_size := last_size * 2 in
    let a := make new_size [] in
    let new_tab := 
      fold_int (fun i a =>
        replace_bucket a (hashtab ht) (PArray.length a) (length ht) i) 
      i a 
    in
    hash_tab (size ht) new_tab.

  Definition resize (ht: t): t :=
    if length ht =? 0 then 
      hash_tab 0 (make 16 [])
    else if resize_heurisitic ht then
      copy_tab ht (length ht)
    else ht.

  Fixpoint bucket_remove (b: bucket) (hash: int) (key: A) :=
    match b with
    | [] => (false, [])
    | e :: b =>
        let (hash', key', _) := e in
        if if hash =? hash' then eq key key' else false
        then (true, b)
        else 
          let new_bucket := bucket_remove b hash key in
          (fst new_bucket, e :: snd new_bucket) 
    end.

  Definition remove (h: t) (key: A) : t :=
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index h hash in
    let bucket := get tab i in
    let b_remove := bucket_remove bucket hash key in
    if fst b_remove
    then hash_tab (size h - 1) (tab.[i <- snd b_remove])
    else h.

  Definition add (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index h hash in
    let bucket := get tab i in
    let new := C hash key v :: tab.[i] in
    hash_tab (size h + 1) tab.[i<-new].

  Definition replace (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index h hash in
    let bucket := get tab i in
    let remove_result := bucket_remove bucket hash key in
    let new_size := if fst remove_result then (size h) else (size h) + 1 in
    hash_tab new_size tab.[i <- C hash key v :: snd remove_result].

  Fixpoint find_rec (l: bucket) (h: int) (k: A): option B :=
    match l with
    | [] => None
    | C h' k' v :: l' => 
        if if h =? h' then eq k k' else false
        then Some v 
        else find_rec l' h k
    end.

  Fixpoint find_all_rec (l: bucket) (h: int) (k: A) (acc: list B): list B :=
    match l with
    | [] => List.rev' acc
    | C h' k' v :: l' => 
        if if h =? h' then eq k k' else false
        then find_all_rec l' h k (v :: acc)
        else find_all_rec l' h k acc
    end.

  Fixpoint find_all_rec' (l: bucket) (h: int) (k: A) : list B :=
    match l with
    | [] => []
    | C h' k' v :: l' => 
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
    + intros acc. simpl. destruct a. case (eq k a) eqn:H.
      - case (h =? i).
        * rewrite IHl. simpl. rewrite <- app_assoc. easy.
        * simpl. apply IHl.
      - case (h =? i).
        * rewrite IHl. reflexivity.
        * apply IHl.
  Qed.

  Definition find (h: t) (key: A) : option B :=
    let hash := hash key in
    let bucket := get_bucket h hash in
    find_rec bucket hash key.

  Definition mem (h: t) (key: A) : bool :=
    match find h key with
    | Some _ => true
    | None   => false
    end.

  Definition find_all (h: t) (key: A) : list B :=
    let hash := hash key in
    find_all_rec (get_bucket h hash) hash key [].

  Lemma replace_bucket_length:
    forall (nt lt: table) i,
    PArray.length (replace_bucket nt lt (PArray.length nt) (PArray.length lt) i) 
    = PArray.length nt.
  Proof.
    intros nt lt i.
    unfold replace_bucket.
    induction lt.[i]; simpl.
    + easy.
    + destruct a.
      case (i =? _ mod (PArray.length lt)); [rewrite length_set|]; apply IHb.
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
      - rewrite eqbP_false_to_Z in *. change (to_Z 0) with 0%Z in *.
        rewrite mul_spec. change (to_Z 2) with 2%Z. rewrite Z.mod_small.
        apply Z.neq_mul_0. split. unfold length in H. exact H. easy.
        generalize (leb_length _ (hashtab ht)). rewrite leb_spec.
        generalize (to_Z_bounded (PArray.length (hashtab ht))). cbn. lia.
      - reflexivity.
    + simpl.
      rewrite replace_bucket_length.
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
          (fun (e : bucket_e) (a0 : array (list bucket_e)) =>
           let (h, _, _) := e in
           if i =? h mod PArray.length (hashtab lt)
           then a0.[h mod PArray.length nt<-e :: a0.[h mod PArray.length nt]]
           else a0) nt b)) = true.
  Proof.
    intros nt lt i0 i b H.
    induction b. simpl. rewrite ltb_spec, mod_spec.
    apply Z.mod_pos_bound. generalize (to_Z_bounded (PArray.length nt)).
    case (eqbP (PArray.length nt) 0) as [| H'] in H; try discriminate.
    change (to_Z 0) with 0%Z in H'.
    change (list bucket_e) with bucket in *. lia.
    simpl. destruct a. case (i =? _). 2: apply IHb.
    rewrite PArray.length_set. apply IHb.
  Qed.

  Lemma replace_bucket_correct1:
    forall (nt: table) (lt: t) (k: A) (i s: int),
    length lt =? 0 = false ->
    PArray.length nt =? 0 = false ->
    i = (hash k) mod (length lt) ->
    find_all (hash_tab s nt) k = [] ->
    find_all (hash_tab s (replace_bucket nt (hashtab lt)
                            (PArray.length nt) (length lt) i)) k =
    find_all lt k.
  Proof.
    intros nt lt j i s Hlt Hnt H Hf.
    unfold find_all, get_bucket, key_index, length.
    simpl. rewrite replace_bucket_length. rewrite Hnt.
    unfold length in Hlt. rewrite Hlt.
    unfold replace_bucket. unfold length in *.
    rewrite <- H.
    induction (hashtab lt).[i].
    - simpl. unfold find_all in Hf.
      unfold get_bucket in Hf. unfold key_index, length in Hf. simpl in Hf.
      rewrite Hnt in Hf.
      rewrite Hf. now simpl.
    - simpl. destruct a.
      case (i =? i0 mod PArray.length (hashtab lt)) eqn:Heq.
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
          case (i0 mod PArray.length nt =? hash j mod PArray.length nt) eqn:Hheq.
          **rewrite eqb_spec in Hheq. rewrite Hheq, get_set_same.
            rewrite 2!find_all_rec_correct. simpl. rewrite Hj. simpl.
            rewrite 2!find_all_rec_correct in IHb. simpl in IHb. apply IHb.
            now apply fold_right_length.
          **rewrite get_set_other. apply IHb. now rewrite eqb_false_spec in Hheq.
      + rewrite IHb. rewrite H in Heq.
        case (eqbP (hash j mod PArray.length (hashtab lt)) 
                (i0 mod PArray.length (hashtab lt))) as [|Heq']in Heq.
        try discriminate.
        rewrite 2!mod_spec in Heq'.
        assert (to_Z (hash j) <> to_Z i0) by (intros H'; now rewrite H' in Heq').
        now case (eqbP (hash j) i0).
  Qed.

  Lemma replace_bucket_correct2:
    forall (nt: table) (lt: t) (k: A) (i s: int),
    length lt =? 0 = false ->
    PArray.length nt =? 0 = false ->
    i <> (hash k) mod (length lt) ->
    (to_Z (length lt) <= to_Z (PArray.length nt))%Z -> 
    find_all (hash_tab s (replace_bucket nt (hashtab lt)
                            (PArray.length nt) (length lt) i)) k =
    find_all (hash_tab s nt) k.
  Proof.
    intros nt lt j i s Hlt Hnt H Hf.
    unfold find_all, get_bucket, key_index, length.
    simpl. rewrite replace_bucket_length. rewrite Hnt.
    unfold replace_bucket. unfold length in *.
    induction (hashtab lt).[i]. now simpl.
    simpl. destruct a. case (i =? i0 mod (PArray.length (hashtab lt))) eqn:Heq.
    2: apply IHb.
    case (i0 mod PArray.length nt =? hash j mod PArray.length nt) eqn:Hm.
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
      (nat_rect (fun _ : nat => table) (make (length ht * 2) [])
        (fun (n0 : nat) (acc : table) =>
          replace_bucket acc (hashtab ht) (PArray.length acc) 
          (length ht) (of_Z (Z.of_nat n0))) n) =? 0 = false.
  Proof.
    intros ht n H.
    induction n. 
    + simpl. rewrite length_make.
      case (length ht * 2 <=? max_length) eqn:H'.
      rewrite eqbP_false_to_Z in *. change (to_Z 0) with 0%Z in *.
      rewrite mul_spec. change (to_Z 2) with 2%Z.
      rewrite Z.mod_small. lia.
      generalize (leb_length _ (hashtab ht)). rewrite leb_spec.
      generalize (to_Z_bounded (length ht)). cbn. lia.
      rewrite eqbP_false_to_Z. cbn. easy.
    + simpl. rewrite replace_bucket_length. apply IHn.
  Qed.

  Lemma length_rect_min:
    forall ht n,
    length ht <=?
      PArray.length
        (nat_rect (fun _ : nat => table) (make (length ht * 2) [])
          (fun (n0 : nat) (acc : table) =>
            replace_bucket acc (hashtab ht) (PArray.length acc) 
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
    + simpl. rewrite replace_bucket_length. apply IHn.
  Qed.
      
  Lemma copy_tab_correct:
    forall (ht: t) (k: A) (i: int),
      length ht =? 0 = false ->
      (hash k) mod length ht <? i = true -> 
      find_all (copy_tab ht i) k = find_all ht k.
  Proof.
    intros ht k i H. unfold length. rewrite ltb_spec. rewrite Z2Nat.inj_lt.
    2: generalize (to_Z_bounded (hash k mod PArray.length (hashtab ht))); lia.
    2: generalize (to_Z_bounded i); lia.
    unfold copy_tab. rewrite fold_int_spec.
    generalize (to_Z_bounded i). intros Hb. destruct Hb as [_ HM].
    rewrite Z2Nat.inj_lt in HM. 3: cbn; lia. 2: generalize (to_Z_bounded i); lia.
    induction (Z.to_nat (to_Z i)).
    + generalize (to_Z_bounded (hash k)). intros Hb.
      rewrite mod_spec, Z2Nat.inj_mod. lia. apply Hb.
      generalize (to_Z_bounded (PArray.length (hashtab ht))).
      intros Hb'. apply Hb'.
    + case (Z.to_nat φ (hash k mod PArray.length (hashtab ht)) <? n)%nat eqn:Hn.
      - simpl. intros _. rewrite replace_bucket_correct2. apply IHn.
        lia. rewrite Nat.ltb_lt in Hn. exact Hn. exact H.
        apply length_rect_non_neg. assumption.
        rewrite <- eqb_false_spec, eqbP_false_to_Z.
        rewrite Nat.ltb_lt in Hn. rewrite Nat2Z.inj_lt, Z2Nat.id in Hn.
        2: generalize (to_Z_bounded (hash k mod PArray.length (hashtab ht))); lia.
        rewrite of_Z_spec, Z.mod_small. 2: lia.
        unfold length. lia.
        rewrite <- leb_spec. apply length_rect_min.
      - simpl. intro H0. apply replace_bucket_correct1. exact H.
        apply length_rect_non_neg. assumption.
        rewrite <- eqb_spec, eqbP_true_to_Z, of_Z_spec, Z.mod_small.
        rewrite Nat.ltb_ge, Nat2Z.inj_le, Z2Nat.id in Hn.
        2: generalize (to_Z_bounded (hash k mod PArray.length (hashtab ht))); lia.
        unfold length. lia. lia. 
        clear IHn H0. rewrite Nat.ltb_ge in Hn.
        induction n.
        * simpl. unfold find_all, get_bucket. simpl.
          case (length _ =? 0). now simpl.
          rewrite get_make. now simpl.
        * simpl. rewrite replace_bucket_correct2. apply IHn. 
          lia. lia. assumption. now rewrite length_rect_non_neg.
          rewrite <- eqb_false_spec, eqbP_false_to_Z.
          rewrite of_Z_spec, Z.mod_small. 2: lia.
          rewrite Nat.le_succ_l, Nat2Z.inj_lt, Z2Nat.id in Hn.
          unfold length. lia.
          generalize (to_Z_bounded (hash k mod PArray.length (hashtab ht))). lia.
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
      set (x:=make 16 []). simpl. unfold x.
      now rewrite get_make.
    - unfold resize, length. rewrite Heqb.
      case resize_heurisitic. 2: reflexivity.
      apply copy_tab_correct.
      unfold length. exact Heqb.
      rewrite ltb_spec, mod_spec.
      apply Z.mod_pos_bound.
      generalize (to_Z_bounded (PArray.length (hashtab h))).
      destruct (eqbP (PArray.length (hashtab h)) 0). discriminate.
      rewrite to_Z_0 in n. lia.
  Qed.

  Theorem hempty:
    forall (k: A) (size: int), find (create size) k = None.
  Proof.
    intros k i. unfold create, find, get_bucket, length. simpl.
    rewrite length_make.
    case (power_2_above i 16 <=? max_length).
    case eqb. now simpl. now rewrite get_make.
    simpl. now rewrite get_make.
  Qed.

  Lemma key_index_eq:
    forall (h1 h2: t) (k: A), 
    length h1 = length h2 ->
    key_index h1 (hash k) = key_index h2 (hash k).
  Proof.
    intros h1 h2 k H. unfold key_index.
    now rewrite H.
  Qed.

  Theorem find_add_same:
    forall (k: A) (v: B) (h: t),
    find_all (add h k v) k = v :: (find_all h k).
  Proof.
    intros k v h. rewrite <- (find_all_resize h).
    unfold find_all.
    rewrite 2!find_all_rec_correct.
    unfold get_bucket.
    rewrite 2!eqb_false_complete.
    rewrite (key_index_eq (add h k v) (resize h)).
    unfold add; simpl. rewrite get_set_same.
    simpl. rewrite eqb_refl. rewrite eq_refl. easy.
    rewrite ltb_spec. apply key_index_max, length_resize_non_neg.
    unfold add; simpl. apply length_set.
    2:unfold add, length; simpl; rewrite length_set.
    all:rewrite <- eqb_false_spec; apply length_resize_non_neg.
  Qed.

  Theorem find_add_diff:
    forall (k k': A) (v: B) (h: t),
    k' <> k -> find_all (add h k v) k' = find_all h k'.
  Proof.
    intros k k' v h Hdiff.
    assert (find_all (resize h) k' = find_all h k'). apply find_all_resize.
    unfold add, find_all, get_bucket, key_index, length in *. simpl.
    rewrite length_set in *. fold (length (resize h)) in *.
    rewrite length_resize_non_neg, find_all_rec_correct in *. simpl in *.
    case (hash k mod length (resize h) =? hash k' mod length (resize h)) eqn:Heq.
    + rewrite eqb_spec in Heq. rewrite <- Heq, get_set_same in *.
      simpl. rewrite eq_false. 2:exact Hdiff.
      replace (if hash k' =? hash k then false else false) with false by now case (hash k' =? hash k). 
      rewrite H. reflexivity.
      rewrite ltb_spec, mod_spec. fold (length (resize h)).
      apply Z.mod_bound_pos. generalize (to_Z_bounded (hash k)). lia.
      generalize (to_Z_bounded (length (resize h))).
      generalize (length_resize_non_neg h). rewrite eqbP_false_to_Z.
      change (to_Z 0) with 0%Z. lia.
    + rewrite eqb_false_spec in Heq. rewrite get_set_other. 2:exact Heq.
      apply H.
  Qed.

  Lemma bucket_remove_same:
    forall (b: bucket) (k: A),
    let h := hash k in
    (fst (bucket_remove b h k) = false -> snd (bucket_remove b h k) = b) /\
    find_all_rec (snd (bucket_remove b h k)) h k []  =
    List.tl (find_all_rec b h k []).
  Proof.
    induction b; intros k h. easy.
    destruct a as [h' k' b']. simpl.
    case (if h =? h' then eq k k' else false) eqn:Hc.
    + destruct (h =? h'); try easy.
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
    induction b; intros k k' h h' Hk. easy.
    destruct a as [hb kb b']. simpl.
    case (if h =? hb then eq k kb else false) eqn:Hc; simpl.
    + assert ((if h' =? hb then eq k' kb else false) = false). 
      { case (h' =? hb). 2:easy. apply eq_false.
        assert (Hkb: eq k kb = true). case (h =? hb) in Hc; easy.
        case (eq_spec k kb) in Hkb; try discriminate.
        rewrite <- e. apply Hk. }
      rewrite H. reflexivity.
    + case (if h' =? hb then eq k' kb else false).
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
    generalize (bucket_remove_same (hashtab ht).[key_index ht (hash k)] k).
    simpl.
    case (bucket_remove (hashtab ht).[key_index ht (hash k)] (hash k) k).
    simpl. intros [|] l [H1 H2]. unfold get_bucket, length. simpl.
    rewrite length_set. case (PArray.length (hashtab ht) =? 0) eqn:Heq.
    reflexivity.
    unfold key_index, length. simpl. rewrite length_set, get_set_same.
    apply H2. rewrite ltb_spec, mod_spec. apply Z_mod_lt.
    rewrite eqbP_false_to_Z in Heq; change (to_Z 0) with 0%Z in Heq.
    generalize (to_Z_bounded (PArray.length (hashtab ht))). lia.
    unfold get_bucket. case (length ht =? 0). reflexivity.
    rewrite <- H1. rewrite <- H1 in H2. exact H2. all:easy.
  Qed.

  Theorem remove_diff:
    forall (ht: t) (k: A) (k': A),
    k' <> k ->
    find_all (remove ht k) k' = find_all ht k'.
  Proof.
    intros ht k k1 Hk. unfold remove, find_all.
    simpl.
    case (fst (bucket_remove (hashtab ht).[key_index ht (hash k)] (hash k) k)).
    simpl. 2:reflexivity.
    unfold get_bucket, key_index, length. simpl. rewrite length_set.
    case (PArray.length (hashtab ht) =? 0) eqn:Hl. reflexivity.
    case (hash k mod PArray.length (hashtab ht) =? 
          hash k1 mod PArray.length (hashtab ht)) eqn:Heq.
    apply eqb_spec in Heq. rewrite Heq. rewrite get_set_same.
    rewrite bucket_remove_other. reflexivity. exact Hk.
    rewrite ltb_spec, mod_spec. apply Z_mod_lt. rewrite eqbP_false_to_Z in Hl.
    change (to_Z 0) with 0%Z in Hl.
    generalize (to_Z_bounded (PArray.length (hashtab ht))). lia. 
    rewrite get_set_other. reflexivity.
    rewrite eqb_false_spec in Heq. exact Heq.
  Qed.

  Theorem find_spec:
    forall ht key,
    find ht key = List.hd_error (find_all ht key).
  Proof.
    intros ht key.
    unfold find_all, find. unfold get_bucket.
    case (length ht =? 0). reflexivity.
    induction (hashtab ht).[key_index ht (hash key)]. reflexivity.
    simpl. destruct a as [h' k' v].
    case (if hash key =? h' then eq key k' else false).
    rewrite find_all_rec_correct. reflexivity.
    apply IHb.
  Qed.

  Theorem replace_same:
    forall ht key v,
    find_all (replace ht key v) key = v :: (List.tl (find_all ht key)).
  Proof.
    intros ht key v. rewrite <- (find_all_resize ht).
    unfold find_all. rewrite 2!find_all_rec_correct.
    unfold get_bucket. rewrite 2!eqb_false_complete. simpl.
    assert (Heq: key_index (resize ht) (hash key) = 
                 key_index (replace ht key v) (hash key)).
    { unfold key_index. unfold length, replace. simpl. now rewrite length_set. }
    rewrite Heq, get_set_same. simpl. rewrite eq_refl, eqb_refl. f_equal.
    generalize (bucket_remove_same
        (hashtab (resize ht)).[key_index (replace ht key v) (hash key)] key).
    simpl. rewrite 2!find_all_rec_correct. simpl. now intros [_ ->].
    rewrite <- Heq. unfold key_index, length. rewrite ltb_spec, mod_spec.
    apply Z_mod_lt. generalize (to_Z_bounded (PArray.length (hashtab (resize ht)))).
    generalize (length_resize_non_neg ht). rewrite eqbP_false_to_Z.
    change (to_Z 0) with 0%Z. unfold length. lia.
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
    unfold replace, find_all, get_bucket, key_index, length. simpl.
    rewrite length_set, Hl.
    case (hash k1 mod PArray.length (hashtab (resize ht)) =?
          hash k2 mod PArray.length (hashtab (resize ht))) eqn:Heq.
    + rewrite eqb_spec in Heq. rewrite Heq. rewrite get_set_same. simpl.
      assert (Hb: (if hash k2 =? hash k1 then eq k2 k1 else false) = false).
      { case (hash k2 =? hash k1). apply neq_sym, eq_false in Hk. all: easy. }
      rewrite Hb, bucket_remove_other. unfold find_all, get_bucket in H.
      rewrite length_resize_non_neg in H. apply H. now apply neq_sym.
      rewrite ltb_spec, mod_spec. apply Z_mod_lt. rewrite eqbP_false_to_Z in Hl.
      generalize (to_Z_bounded (PArray.length (hashtab (resize ht)))).
      change (to_Z 0) with 0%Z in Hl. lia.
    + rewrite get_set_other. unfold find_all, get_bucket in H.
      rewrite length_resize_non_neg in H. apply H. rewrite eqb_false_spec in Heq.
      apply Heq.
  Qed.

End Hashtable.

