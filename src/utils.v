Require Import Coq.Lists.List.
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

