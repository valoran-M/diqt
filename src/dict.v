Require Import Bool.
Require Import ZArith.
Require Import Zdiv.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import radix.
Require Import utils.

Section Dict.
  Variable A: Set.
  Variable eq: A -> A -> bool.
  Variable eq_spec: forall x y : A, reflect (x = y) (eq x y).
  Variable B: Set.

  Variable hash: A -> positive.

  Inductive bucket : Set :=
    | E : bucket
    | C : positive -> A -> B -> bucket -> bucket.
  Definition t := tree bucket.

  Definition empty : t := empty.

  Fixpoint find_iter h_k k l: option B :=
    match l with
    | E     => None
    | C h k' v tl =>
        if h_k =? h
        then ( if eq k k'
               then Some v
               else find_iter h_k k tl)
        else find_iter h_k k tl
    end.

  Definition find (k: A) (d: t): option B :=
    match get (hash k) d with
    | None   => None
    | Some l => find_iter (hash k) k l
    end.

  Fixpoint find_all_rec (l: bucket) (h: positive) (k: A) (acc: list B): list B :=
    match l with
    | E => List.rev' acc
    | C h' k' v l' => 
        if if h =? h' then eq k k' else false
        then find_all_rec l' h k (v :: acc)
        else find_all_rec l' h k acc
    end.

  Definition find_all (k: A) (d: t): list B :=
    let h_k := hash k in
    match get h_k d with
    | None   => []
    | Some l => find_all_rec l h_k k []
    end.

  Definition add (k: A) (e: B) (d: t): t :=
    let h_k := hash k in
    match get h_k d with
    | None   => set h_k (C h_k k e E) d
    | Some l => set h_k (C h_k k e l) d
    end.

  Fixpoint bucket_remove (b: bucket) (hash: positive) (key: A) :=
    match b with
    | E => E
    | C hash' key' v b =>
        if if hash =? hash' then eq key key' else false
        then b
        else C hash' key' v (bucket_remove b hash key)
    end.

  Definition remove (k: A) (d: t): t :=
    let h_k := hash k in
    match get h_k d with
    | None   => d
    | Some l => set h_k (bucket_remove l h_k k) d
    end.

  Definition replace (k: A) (e: B) (d: t): t :=
    let h_k := hash k in
    match get h_k d with
    | None   => set h_k (C h_k k e E) d
    | Some l => set h_k (C h_k k e (bucket_remove l h_k k)) d
    end.

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

  Theorem dempty:
    forall (k: A), find k empty = None.
  Proof.
    intro i. unfold find.
    assert (get (hash i) empty = None).
    apply gempty. now rewrite H.
  Qed.

  Theorem dss:
    forall (k: A) (x: B) (d: t), find k (add k x d) = Some x.
  Proof.
    intros k x d. unfold find, add.
    case (get (hash k) d).
    - intro l. rewrite gss. simpl.
      case (eq_spec k k). intros Hk.
      assert (H: hash k =? hash k = true) by now rewrite Pos.eqb_eq.
      now rewrite H.
      intros Hk. contradiction.
    - rewrite gss. simpl.
      case (eq_spec k k); intros Hk.
      assert (H: hash k =? hash k = true) by now rewrite Pos.eqb_eq.
      now rewrite H. contradiction.
  Qed.

  Lemma hash_equal:
    forall (k1 k2: A) (x: B) (d: t) l,
      hash k1 = hash k2 ->
      get (hash k1) d = Some l ->
      get (hash k1) (add k2 x d) = Some (C (hash k2) k2 x l).
  Proof.
    intros k1 k2 x d l H Hget.
    unfold add. rewrite <- H. rewrite Hget.
    apply gss.
  Qed.

  Lemma hash_diff:
    forall (k1 k2: A) (x: B) (d: t) l,
      hash k1 <> hash k2 ->
      get (hash k1) d = l ->
      get (hash k1) (add k2 x d) = l.
  Proof.
    intros k1 k2 x d l H Hget. rewrite <- Hget.
    unfold add. case (get (hash k2) d).
    intro l0. now apply gso.
    now apply gso.
  Qed.

  Theorem dso:
    forall (k1 k2: A) (x: B) (d: t),
      k1 <> k2 -> find k1 (add k2 x d) = find k1 d.
  Proof.
    intros k1 k2 x d H. unfold find.
    case (Pos.eq_dec (hash k1) (hash k2)).
    - intros Heq.
      destruct (get (hash k1) d) eqn:Hget.
      rewrite hash_equal with (1 := Heq) (2 := Hget).
      simpl. rewrite <- Pos.eqb_eq in Heq. rewrite Heq.
      assert (H0: eq k1 k2 = false) by now rewrite eq_false.
      now rewrite H0.
      unfold add. rewrite <- Heq, Hget. rewrite gss. simpl.
      assert (H0: hash k1 =? hash k1 = true) by now rewrite Pos.eqb_eq.
      rewrite H0. assert (H1: eq k1 k2 = false) by now rewrite eq_false.
      now rewrite H1.
    - intro Hdiff. case (get (hash k1) d) eqn:Hget;
      now rewrite hash_diff with (1 := Hdiff) (2 := Hget).
  Qed.
End Dict.

