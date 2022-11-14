Definition is_some {A : Type} (o : option A) : bool :=
  if o then true else false.

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).
#[global] Hint Unfold compose : core.
Notation "g * f" := (compose g f)
  (at level 40, left associativity).
