From Coq Require Import MSets.
From Coq Require Import Arith.Arith.
From KapCake Require Import NatMap.
From KapCake Require Import Rel.

Module NatSet := Make Nat_as_OT.
Module D := MSetDecide.Decide NatSet.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof. intros n m. apply iff_reflect.
       rewrite Nat.eqb_eq. reflexivity. Qed.

Module NatSetMap.

Record t : Type :=
  mkMap { dom : NatSet.t
        ; cod : NatSet.t
        ; map : NatMap.partial nat
    }.

Definition empty :=
  {| dom := NatSet.empty
  ;  cod := NatSet.empty
  ;  map := NatMap.empty
  |}.

Definition is_total (m : t) : Prop :=
  forall x, NatSet.In x (dom m) -> exists u,
      NatSet.In u (cod m) /\ map m x = Some u.

Lemma empty_is_total : is_total empty.
Proof. easy. Qed.

End NatSetMap.

Module NatSetRel.

Record t : Type :=
  mkRel { over : NatSet.t
        ; rel : Rel.t nat
    }.

Definition empty :=
  {| rel := Rel.empty
  ;  over := NatSet.empty
  |}.

Definition in_dom (r : t) : Prop := forall x y,
    In (x, y) r.(rel) ->
    NatSet.In x r.(over) /\ NatSet.In y r.(over).

Lemma empty_in_dom : in_dom empty.
Proof. easy. Qed.

End NatSetRel.
