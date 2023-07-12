Require Import ZArith.
Require Import Coq.ssr.ssrbool.
Require Import int_utils.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope positive_scope.

Section Radix.
  Variable A: Set.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable B: Set.

  Variable hash: A -> positive.

  Inductive bucket : Set :=
  | B_Empty : bucket
  | B_Cons : positive -> A -> B -> bucket -> bucket.

  Inductive tree : Type :=
  | Empty: tree
  | Node:  tree -> bucket -> tree -> tree.

  (** ** Tree functions *)

  Definition empty : tree := Empty.

  Fixpoint get (p: positive) (t: tree) : bucket :=
    match p, t with
    | _,     Empty      => B_Empty
    | xH,    Node _ e _ => e
    | xO p', Node l _ _ => get p' l
    | xI p', Node _ _ r => get p' r
    end.

  Fixpoint set0 (p: positive) (e: bucket) : tree :=
    match p with
    | xH    => Node Empty e Empty
    | xO p' => Node (set0 p' e) B_Empty Empty
    | xI p' => Node Empty B_Empty (set0 p' e)
    end.

  Fixpoint set (p: positive) (e: bucket) (t: tree) : tree :=
    match p, t with
    | _,     Empty      => set0 p e
    | xH,    Node l _ r => Node l e r
    | xO p', Node l y r => Node (set p' e l) y r
    | xI p', Node l y r => Node l y (set p' e r)
    end.

  (** ** Tree Facts *)

  Theorem gempty:
    forall (i: positive), get i empty = B_Empty.
  Proof.
    intro i. case i; reflexivity.
  Qed.

  Theorem gss0:
    forall (i: positive) (x: bucket), get i (set0 i x) = x.
  Proof.
    intros i x. induction i; simpl; auto.
  Qed.

  Theorem gos0:
    forall (i j: positive) (x: bucket),
    i <> j -> get i (set0 j x) = B_Empty.
  Proof.
    induction i; intros j x H; simpl.
    - destruct j; simpl; [apply IHi; now intros <-| |]; apply gempty.
    - destruct j; simpl; [| apply IHi; now intros <-|]; apply gempty.
    - destruct j; now simpl.
  Qed.


  Theorem gss:
    forall (i: positive) (x: bucket) (t: tree), get i (set i x t) = x.
  Proof.
    induction i; destruct t; simpl; auto; try apply IHi; now rewrite gss0.
  Qed.

  Theorem gso:
    forall (i j: positive) (x: bucket) (t: tree),
    i <> j -> get i (set j x t) = get i t.
  Proof.
    induction i; intros j x t H; destruct j, t;
    try auto using go0s; try apply gempty; try easy.
    - apply gos0. assumption.
    - apply IHi. now intros <-.
    - apply gos0. assumption.
    - apply IHi. now intros <-.
  Qed.

  (** ** hashtables functions *)

  Fixpoint find_rec l h k: option B :=
    match l with
    | B_Empty => None
    | B_Cons h' k' v tl =>
        if if h =? h' then eq k k' else false
        then Some v
        else find_rec tl h k
    end.

  Definition find (t: tree) (k: A) : option B :=
    let h := hash k in
    find_rec (get h t) h k.

  Fixpoint find_all_rec (l: bucket) (h: positive) (k: A) (acc: list B): list B :=
    match l with
    | B_Empty => List.rev' acc
    | B_Cons h' k' v l' =>
        if if h =? h' then eq k k' else false
        then find_all_rec l' h k (v :: acc)
        else find_all_rec l' h k acc
    end.

  Definition mem (h: tree) (key: A) : bool :=
    match find h key with
    | Some _ => true
    | None   => false
    end.

  Definition find_all (d: tree) (k: A) : list B :=
    let h_k := hash k in
    find_all_rec (get h_k d) h_k k nil.

  Definition add (d: tree) (k: A) (e: B) : tree :=
    let h_k := hash k in
    match get h_k d with
    | B_Empty => set h_k (B_Cons h_k k e B_Empty) d
    | b       => set h_k (B_Cons h_k k e b) d
    end.

  Fixpoint bucket_remove (b: bucket) (h: positive) (k: A) :=
    match b with
    | B_Empty => B_Empty
    | B_Cons h' k' v b =>
        if if h =? h' then eq k k' else false
        then b
        else B_Cons h' k' v (bucket_remove b h k)
    end.

  Definition remove (d: tree) (k: A) : tree :=
    let h := hash k in
    match get h d with
    | B_Empty => d
    | b       => set h (bucket_remove b h k) d
    end.

  Definition replace (d: tree) (k: A) (e: B) : tree :=
    let h := hash k in
    match get h d with
    | B_Empty => set h (B_Cons h k e B_Empty) d
    | b       => set h (B_Cons h k e (bucket_remove b h k)) d
    end.

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
    forall (k : A), k = k -> eq k k = true.
  Proof.
    intros k H.
    now case eq_spec.
  Qed.

  (** find_all *)

  Fixpoint find_all_rec' (l: bucket) (h: positive) (k: A) : list B :=
    match l with
    | B_Empty => nil
    | B_Cons h' k' v l' =>
        if if h =? h' then eq k k' else false
        then v :: find_all_rec' l' h k
        else find_all_rec' l' h k
    end.

  Lemma find_all_rec_correct:
    forall (l: bucket) (h: positive) (key: A) acc,
    find_all_rec l h key acc = rev acc ++ find_all_rec' l h key.
  Proof.
    intros l h k.
    induction l.
    + intros acc. simpl. apply rev_append_rev.
    + intros acc. simpl. case (eq k a) eqn:H.
      - case (h =? p).
        * rewrite IHl. simpl. rewrite <- app_assoc. easy.
        * simpl. apply IHl.
      - case (h =? p).
        * rewrite IHl. reflexivity.
        * apply IHl.
  Qed.

  (** empty *)

  Theorem find_empty:
    forall (k: A), find empty k = None.
  Proof.
    intro i. unfold find.
    assert (get (hash i) empty = B_Empty).
    apply gempty. now rewrite H.
  Qed.

  (** add *)

  Theorem find_add_same:
    forall (d: tree) (k: A) (v: B),
    find_all (add d k v) k = v :: find_all d k.
  Proof.
    intros d k x. unfold find_all, add.
    rewrite 2!find_all_rec_correct. simpl.
    case (get (hash k) d).
    - rewrite gss. simpl.
      case (eq_spec k k). intros Hk.
      assert (H: hash k =? hash k = true) by now rewrite Pos.eqb_eq.
      now rewrite H.
      intros Hk. contradiction.
    - intros *. rewrite gss. simpl.
      case (eq_spec k k); intros Hk. 2:contradiction.
      assert (H: hash k =? hash k = true) by now rewrite Pos.eqb_eq.
      now rewrite H.
  Qed.

  Theorem find_add_other:
    forall (d: tree) (k k': A) (v: B),
    k' <> k -> find_all (add d k v) k' = find_all d k'.
  Proof.
    intros d k k' v. intros Hk. unfold find_all, add.
    rewrite 2!find_all_rec_correct. simpl.
    case (hash k =? hash k') eqn:Hh.
    - apply Peqb_true_eq in Hh. rewrite Hh. case (get (hash k') d).
      * rewrite gss. simpl. rewrite Pos.eqb_refl.
        now rewrite (eq_false k' k Hk).
      * intros *. rewrite gss.
        simpl. rewrite Pos.eqb_refl. now rewrite (eq_false k' k Hk).
    - rewrite Pos.eqb_neq in Hh. case (get (hash k) d).
      * rewrite gso. easy.
        intros H; apply Hh; now rewrite H.
      * intros *. rewrite gso. easy.
        intros H; apply Hh; now rewrite H.
  Qed.

  (** find *)

  Theorem find_spec:
    forall t key,
    find t key = List.hd_error (find_all t key).
  Proof.
    intros t key.
    unfold find_all, find.
    induction (get (hash key) t). easy.
    simpl. case (if hash key =? p then eq key a else false).
    + now rewrite find_all_rec_correct.
    + apply IHb.
  Qed.

  (** remove  *)

  Lemma bucket_remove_same:
    forall (b: bucket) (k: A),
    let h := hash k in
    find_all_rec (bucket_remove b h k) h k []  =
    List.tl (find_all_rec b h k []).
  Proof.
    induction b; intros k h. easy. simpl.
    case (if h =? p then eq k a else false) eqn:Hc.
    + destruct (h =? p); try easy.
      rewrite 2!find_all_rec_correct. easy.
    + simpl. rewrite Hc. apply IHb.
  Qed.

  Lemma bucket_remove_other:
    forall (b: bucket) (k k': A),
    let h := hash k in
    let h' := hash k' in
    k' <> k ->
    find_all_rec (bucket_remove b h k) h' k' []  =
    find_all_rec b h' k' [].
  Proof.
    induction b; intros k k' h h' Hk. easy. simpl.
    case (if h =? p then eq k a else false) eqn:Hc; simpl.
    + assert ((if h' =? p then eq k' a else false) = false).
      { case (h' =? p). 2:easy. apply eq_false.
        assert (Hkb: eq k a = true). case (h =? p) in Hc; easy.
        case (eq_spec k a) in Hkb; try discriminate.
        rewrite <- e. apply Hk. }
      rewrite H. reflexivity.
    + case (if h' =? p then eq k' a else false).
      - rewrite 2!find_all_rec_correct. f_equal.
        rewrite <- app_nil_l at 1. rewrite <- app_nil_l.
        assert (H:@rev (list B) [] = []). reflexivity.
        change [] with (@rev B []).
        rewrite <- 2!find_all_rec_correct. apply IHb. exact Hk.
      - apply IHb. exact Hk.
  Qed.

  Theorem remove_same:
    forall (t: tree) (k: A),
    find_all (remove t k) k =
    List.tl (find_all t k).
  Proof.
    intros t k. unfold remove, find_all.
    rewrite 2!find_all_rec_correct. simpl.
    case (get (hash k) t) eqn:H. now rewrite H.
    generalize (bucket_remove_same (get (hash k) t) k). simpl.
    case (if hash k =? p then eq k a else false) eqn:Heq.
    + simpl. now rewrite gss.
    + simpl. rewrite 2!find_all_rec_correct. rewrite H. simpl.
      rewrite gss. simpl. rewrite Heq. simpl. now rewrite Heq.
  Qed.

  Theorem remove_other:
    forall (t: tree) (k: A) (k': A),
    k' <> k ->
    find_all (remove t k) k' = find_all t k'.
  Proof.
    intros *. unfold remove, find_all. intros Hk.
    case (get (hash k) t) eqn:H. easy.
    case (hash k =? hash k') eqn:Hh.
    + apply Peqb_true_eq in Hh. rewrite Hh at 1. rewrite gss.
      rewrite bucket_remove_other. 2:easy. rewrite <- Hh. now rewrite H.
    + rewrite gso. easy. apply not_eq_sym. now apply Pos.eqb_neq.
  Qed.


  (** replace *)

  Theorem replace_same:
    forall h key v,
    find_all (replace h key v) key = v :: (List.tl (find_all h key)).
  Proof.
    intros h key v. unfold find_all, replace.
    case (get (hash key) h).
    + rewrite gss. simpl. now rewrite Pos.eqb_refl, eq_refl.
    + intros *. rewrite gss. simpl. rewrite Pos.eqb_refl, eq_refl. 2: easy.
      f_equal. case (if hash key =? p then eq key a else false) eqn:H.
      * rewrite 2!find_all_rec_correct. reflexivity.
      * simpl. rewrite H. rewrite <- bucket_remove_same, 2!find_all_rec_correct.
        reflexivity.
  Qed.

  Theorem replace_other:
    forall h k1 k2 v,
    k1 <> k2 ->
    find_all (replace h k1 v) k2 = find_all h k2.
  Proof.
    intros h k1 k2 v Hk. unfold find_all, replace.
    case (hash k1 =? hash k2) eqn:Hh.
    + case (get (hash k1) h) eqn:Hg; apply Peqb_true_eq in Hh.
      * rewrite 2!find_all_rec_correct. simpl.
        rewrite <- Hh, Hg. rewrite gss. simpl.
        rewrite Pos.eqb_refl, eq_false. easy.
        now apply not_eq_sym.
      * rewrite Hh. rewrite gss.
        simpl. rewrite Pos.eqb_refl, eq_false.
        2:intros H; apply Hk; now rewrite H.
        rewrite <- Hh, Hg. simpl.
        case (hash k1 =? p) eqn:Heq.
        - case (eq k1 a) eqn:Hk1.
          **rewrite eq_false. easy.
            case (eq_spec k1 a) in Hk1; try discriminate.
            rewrite <- e. now apply not_eq_sym.
          **simpl. rewrite Heq.
            generalize (bucket_remove_other b0 k1 k2). simpl.
            rewrite 6!find_all_rec_correct. simpl. intros H.
            case (eq k2 a). f_equal.
            all: rewrite Hh at 2; rewrite H, Hh. 1,3: easy.
            all: now apply not_eq_sym.
        - simpl. rewrite Hh at 5. rewrite bucket_remove_other.
          now rewrite Heq, Hh. now apply not_eq_sym.
    + case (get (hash k1) h).
      * rewrite gso. easy.
        apply Pos.eqb_neq in Hh.
        apply (not_eq_sym Hh).
      * intros *. rewrite gso. easy.
        apply Pos.eqb_neq in Hh.
        apply (not_eq_sym Hh).
  Qed.
End Radix.

Arguments tree A : clear implicits.

