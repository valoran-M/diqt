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

  Definition t := tree (list (A * B)).

  Definition empty : t := empty.

  Definition find (k: A) (d: t): option B :=
    match get (hash k) d with
    | None   => None
    | Some l => find_snd A B (fun '(k', _) => eq k k') l
    end.

  Definition add (k: A) (e: B) (d: t): t := 
    let h_k := hash k in
    match get h_k d with
    | None   => set h_k [(k, e)] d
    | Some l => set h_k ((k, e)::l) d
    end.
  
  Search reflect.

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
      case (eq_spec k k). now intro. contradiction.
    - rewrite gss. simpl.
      case (eq_spec k k). now intro. contradiction.
  Qed.

  Lemma hash_equal:
    forall (k1 k2: A) (x: B) (d: t) (l: list (A * B)),
      hash k1 = hash k2 -> 
      get (hash k1) d = Some l -> 
      get (hash k1) (add k2 x d) = Some ((k2, x) :: l).
  Proof.
    intros k1 k2 x d l H Hget.
    unfold add. rewrite <- H. rewrite Hget.
    apply gss.
  Qed.

  Lemma hash_diff:
    forall (k1 k2: A) (x: B) (d: t) (l: option (list (A *B))),
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
      simpl. case (eq_spec k1 k2). easy. now intros _.
      rewrite Heq. unfold add.
      rewrite <- Heq, Hget. rewrite gss. simpl.
      case (eq_spec k1 k2). easy. now intros _.
    - intro Hdiff. case (get (hash k1) d) eqn:Hget;
      now rewrite hash_diff with (1 := Hdiff) (2 := Hget).
  Qed.
End Dict.

