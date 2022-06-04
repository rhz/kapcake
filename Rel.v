From Coq Require Import Lists.List.
Import ListNotations.

Module Rel.

Definition t (A : Type) : Type := list (A * A).
Definition empty {A : Type} : t A := [].

Definition is_symmetric {A : Type} (rel : t A) : Prop :=
  forall x y, In (x, y) rel -> In (y, x) rel.

Lemma empty_is_symmetric : forall {A : Type},
    @is_symmetric A empty.
Proof. easy. Qed.

End Rel.
