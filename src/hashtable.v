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
Print int.
Check to_Z.

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

  Print eq_sym.

  Lemma neq_sym:
    forall (k k' : A), k <> k' -> k' <> k.
  Proof.
    intros k k' H. intro nH.
    apply H. now apply eq_sym.
  Qed.

  Inductive bucket_e : Set :=
    | C : int -> A -> B  -> bucket_e
  .
  Definition bucket := list (bucket_e).
  Definition table := PArray.array bucket.
  
  Record t : Set := hash_tab { 
    size : int;
    hashtab : table; 
  }.

  Definition length t : int :=
    PArray.length (hashtab t).

  Fixpoint bucket_well_formed (b: bucket) (i: int) (l: int) : bool :=
    match b with
    | [] => true
    | C h k _ :: b' => 
        (hash k =? h)
        && (i =? (h land (l - 1))) 
        && bucket_well_formed b' i l
    end.

  Definition well_formed (h: t) : Prop :=
    0 <? PArray.length (hashtab h) = true /\ 
    forall i, bucket_well_formed (hashtab h).[i] i 
              (length h) = true.

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
    (to_Z (key_index h k) < to_Z (PArray.length (hashtab h)))%Z.
  Proof.
    admit.
  Admitted.

  Definition get_bucket (h: t) (k: int) : bucket :=
    if length h =? 0 then []
    else (hashtab h).[key_index h k].

  Definition resize_heurisitic (h: t) : bool :=
    false. 

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

  Lemma length_resize:
    forall (h: t),
    (0 < to_Z (length (resize h)))%Z.
  Proof.
    admit.
  Admitted.

  Lemma length_resize_non_neg:
    forall (h: t),
    (length (resize h)) <> 0.
  Proof.
    admit.
  Admitted.

  Definition add (h: t) (key: A) (v: B) : t :=
    let h := resize h in
    let tab := hashtab h in
    let hash := hash key in
    let i := key_index h hash in
    let bucket := get tab i in
    let new := C hash key v :: tab.[i] in
    hash_tab (size h + 1) tab.[i<-new].

  Fixpoint find_rec (l: bucket) (h: int) (k: A): option B :=
    match l with
    | [] => None
    | C h' k' v :: l' => 
        if andb (h =? h') (eq k k')
        then Some v 
        else find_rec l' h k
    end.

  Fixpoint find_all_rec (l: bucket) (h: int) (k: A) (acc: list B): list B :=
    match l with
    | [] => List.rev' acc
    | C h' k' v :: l' => 
        if andb (h =? h') (eq k k')
        then find_all_rec l' h k (v :: acc)
        else find_all_rec l' h k acc
    end.

  Fixpoint find_all_rec' (l: bucket) (h: int) (k: A) : list B :=
    match l with
    | [] => []
    | C h' k' v :: l' => 
        if andb (h =? h') (eq k k')
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
    + intros acc. simpl. destruct a. case (_ && _).
      rewrite IHl. simpl. rewrite <- app_assoc. easy.
      apply IHl.
  Qed.

  Definition find (h: t) (key: A) : option B :=
    let hash := hash key in
    let bucket := get_bucket h hash in
    find_rec bucket hash key.

  Definition find_all (h: t) (key: A) : list B :=
    let hash := hash key in
    find_all_rec (get_bucket h hash) hash key [].

  Lemma mult_size_non_neg:
    forall (ht: t), 
    PArray.length (hashtab ht) =? 0 = false ->
    PArray.length (hashtab ht) * 2 =? 0 = false.
  Proof.
    intros ht H.
    case (eqbP (PArray.length (hashtab ht)) 0) as [|H'] in H; try discriminate.
    rewrite eqb_false_spec. intro Hd. apply H'.
    case (eqbP (PArray.length (hashtab ht) * 2) 0) as [Hd'|Hd'] in Hd;
    rewrite mul_spec in Hd'; change (to_Z 2) with 2%Z in Hd';
    change (to_Z 0) with 0%Z in *. 
  Admitted.

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
    length ht =? 0 = false ->
    length (copy_tab ht i) =? 0 = false.
  Proof.
    intros ht i H.
    unfold copy_tab, length. simpl.
    rewrite fold_int_spec.
    induction (Z.to_nat (to_Z i)).
    + simpl. rewrite length_make.
      case (_ <=? _).
      - now apply mult_size_non_neg.
      - reflexivity.
    + simpl.
      rewrite replace_bucket_length.
      apply IHn.
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
          rewrite get_set_same. simpl. rewrite eqb_refl, andb_true_l.
          case (eq j a); rewrite 2!find_all_rec_correct in IHb; simpl in IHb;
          rewrite 2!find_all_rec_correct; apply f_equal;
          rewrite <- Hj; apply IHb. now apply fold_right_length.
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
    induction (Z.to_nat (to_Z i)).
    + generalize (to_Z_bounded (hash k)). intros Hb.
      rewrite mod_spec, Z2Nat.inj_mod. lia. easy.
      generalize (to_Z_bounded (PArray.length (hashtab ht))).
      now intros Hb'.
    + case (Z.to_nat φ (hash k mod PArray.length (hashtab ht)) <? n)%nat eqn:Hn.
      - simpl. intros _. rewrite replace_bucket_correct'. apply IHn.
        now rewrite Nat.ltb_lt in Hn.
        induction n. simpl. rewrite length_make.
        * case (_ <=? max_length). 2: apply leb_length.
          rewrite leb_spec, mul_spec. change (to_Z 2) with 2%Z.
          rewrite Z.mod_small. generalize (to_Z_bounded (length ht)). lia.
          split. generalize (to_Z_bounded (length ht)). lia.
          apply Z.le_lt_trans with (m:=(to_Z PArray.max_length * 2)%Z).
          unfold length. apply Zmult_le_compat_r.
          rewrite <- leb_spec. apply leb_length. lia. cbn. easy.
        * simpl. admit.
      - simpl. intro H0. apply replace_bucket_correct. admit.
  Qed.

  Lemma find_all_resize:
    forall (h: t) (k: A),
    find_all (resize h) k = find_all h k.
  Proof.
    intros h k.
    case (PArray.length (hashtab h) =? 0) eqn:Heqb.
    - unfold resize, find_all, get_bucket.
      rewrite Heqb.
      set (x:=make 16 []). simpl. unfold x.
      now rewrite get_make.
    - unfold resize. rewrite Heqb.
      case resize_heurisitic. 2: reflexivity.
      apply find_all_copy_tab.
      rewrite ltb_spec, mod_spec.
      apply Z.mod_pos_bound.
      generalize (to_Z_bounded (PArray.length (hashtab h))).
      destruct (eqbP (PArray.length (hashtab h)) 0). discriminate.
      rewrite to_Z_0 in n. lia.
  Qed.

  Theorem hempty:
    forall (k: A) (size: int), find (create size) k = None.
  Proof.
    intros k i. unfold create, find, get_bucket. simpl.
    rewrite length_make.
    case (power_2_above i 16 <=? max_length).
    case eqb. now simpl. now rewrite get_make.
    simpl. now rewrite get_make.
  Qed.

  Lemma key_index_eq:
    forall (h1 h2: t) (k: A), 
    PArray.length (hashtab h1) = PArray.length (hashtab h2) ->
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
    rewrite ltb_spec. apply key_index_max.
    unfold add; simpl. apply length_set.
    2:unfold add; simpl; rewrite length_set.
    all:apply length_resize_non_neg.
  Qed.

  Theorem find_add_diff:
    forall (k k': A) (v: B) (h: t),
    k <> k' -> find_all (add h k v) k' = find_all h k'.
  Proof.
    intros k k' v h Hdiff.
    unfold add, find_all, get_bucket. simpl.
    rewrite length_set.
    rewrite eqb_false_complete; [|apply length_resize_non_neg].
    case (PArray.length (hashtab h) =? 0) eqn:H.
    + unfold resize, key_index. rewrite H. set (m:=make 16 []).
      simpl.
      rewrite length_set. simpl.
      case (hash k' land 15 =? hash k land 15) eqn:Hhk.
      - apply eqb_correct in Hhk.
        rewrite Hhk, get_set_same. simpl.
        rewrite eq_false. 
        assert ((hash k' =? hash k) && false = false).
        apply andb_false_iff; now right.
        rewrite H0. unfold m. rewrite get_make. now simpl.
        now apply neq_sym.
        rewrite ltb_spec. unfold m. simpl. admit.
      - unfold m. rewrite get_make, get_set_other.
        rewrite get_make. now simpl.
        rewrite  eqb_false_spec in Hhk.
        intro Hd. apply eq_sym in Hd.
        now apply Hhk.
    + unfold resize, key_index. rewrite H. simpl.
      rewrite length_set.
      case (hash k land (PArray.length (hashtab h) - 1) =? 
            hash k' land (PArray.length (hashtab h) - 1)) eqn:Heq.
      - apply eqb_spec in Heq. rewrite Heq, get_set_same. simpl.
        rewrite eq_false; [|now apply neq_sym].
        assert ((hash k' =? hash k) && false = false).
        apply andb_false_iff; now right.
        rewrite H0. easy. admit.
      - apply eqb_false_spec in Heq. rewrite get_set_other. easy. easy.
  Admitted.

End Hashtable.

Module Type Hash_type.
  Variable A: Set.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable hash: A -> int.
End Hash_type.

Module HashTable (T: Hash_type).
  Definition t := @t T.A.
  Definition create (B: Set) (initial_size: int) : t B :=
    create initial_size.

  Definition add {B: Set} (h: t B) (key: T.A) (v: B) :=
    add T.hash h key v.

  (* Definition find {B: Set} (h: t B) (key: T.A): option B := *)
  (*   find T.eq T.hash key h. *)
End HashTable.

