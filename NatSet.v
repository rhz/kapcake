From Coq Require Import MSets.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From KapCake Require Import NatMap.
From KapCake Require Import Rel.
From KapCake Require Import Tactics.

Module NatSet := Make Nat_as_OT.
Module D := MSetDecide.Decide NatSet.

(* FIXME: is this the place to have `eqbP`? *)
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof. intros n m. apply iff_reflect.
       rewrite Nat.eqb_eq. reflexivity. Qed.

(* Extend `NatMap`s for the case where the domain and codomain
   are `NatSet`s.
 *)
Module NatMap.
Include NatMap.

(* In the case where the domain and codomain are `NatSet`s
   we are working with `partial nat`s. Here's a shortcut. *)
Definition t := partial nat.

Definition is_total (m : t) (dom cod : NatSet.t) : Prop :=
  forall x, NatSet.In x dom -> exists u,
      NatSet.In u cod /\ m x = Some u.

Lemma empty_is_total : is_total empty NatSet.empty NatSet.empty.
Proof. easy. Qed.

Import PartialMapNotation.

Lemma update_pres_is_total : forall m dom cod x v,
    NatSet.In x dom ->
    NatSet.In v cod ->
    is_total m dom cod ->
    is_total (x |-> v; m) dom cod.
Proof.
  unfold is_total. introv xInDom vInCod H. intros x' H'.
  destruct (eqbP x x') as [eq_xx' | neq_xx'].
  - exists v. split. apply vInCod.
    rewrite eq_xx'. apply update_eq.
  - destruct (H x' H') as [u [H1 H2]]. exists u. split.
    apply H1. rewrite update_neq. apply H2. apply neq_xx'.
Qed.

Lemma add_cod_pres_is_total : forall m dom cod x,
    is_total m dom cod -> is_total m dom (NatSet.add x cod).
Proof.
  unfold is_total. introv H. intros x' H'.
  destruct (H x' H') as [u [H1 H2]]. exists u.
  split. apply D.F.add_2. apply H1. apply H2.
Qed.

Definition is_total_b (m : t) (dom cod : NatSet.t) : bool :=
  NatSet.for_all (fun x => match m x with
                           | None => false
                           | Some u => NatSet.mem u cod
                           end) dom.

Lemma is_total_spec_1 : forall m dom cod,
    is_total m dom cod -> is_total_b m dom cod = true.
Proof.
  unfold is_total, is_total_b. introv H.
  apply NatSet.for_all_spec. solve_proper.
  unfold NatSet.For_all. introv xInDom.
  destruct (H x xInDom) as [u [H1 H2]].
  rewrite H2. apply NatSet.mem_spec. apply H1.
Qed.

Lemma is_total_spec_2 : forall m dom cod,
    is_total_b m dom cod = true -> is_total m dom cod.
Proof.
  unfold is_total, is_total_b. introv H.
  apply NatSet.for_all_spec in H; try solve_proper.
  unfold NatSet.For_all in H.
  introv xInDom. specialize (H x xInDom) as H1.
  destruct (m x) as [u|] eqn:eq_mx.
  - exists u. split.
    + apply NatSet.mem_spec. apply H1.
    + reflexivity.
  - discriminate H1.
Qed.

Corollary is_total_spec : forall m dom cod,
    is_total m dom cod <-> is_total_b m dom cod = true.
Proof.
  introv. split.
  - apply is_total_spec_1.
  - apply is_total_spec_2.
Qed.

Theorem is_totalP : forall m dom cod,
    reflect (is_total m dom cod) (is_total_b m dom cod).
Proof.
  introv. apply iff_reflect.
  rewrite is_total_spec. reflexivity.
Qed.

End NatMap.

(* Extend `Rel`s for the case where the set over which
   the relation is defined is a `NatSet`.

  `SRel` stands for symmetric relation.
 *)
Module NatSRel.

Definition t := Rel.t nat.
Definition empty : t := Rel.empty.
Definition is_symmetric (rel : t) : Prop :=
  forall x y, In (x, y) rel -> In (y, x) rel.
Lemma empty_is_symmetric : is_symmetric empty.
Proof. exact Rel.empty_is_symmetric. Qed.

Definition in_dom (rel : t) (dom : NatSet.t) : Prop :=
  forall x y, In (x, y) rel ->
              NatSet.In x dom /\ NatSet.In y dom.

Lemma empty_in_dom : in_dom empty NatSet.empty.
Proof. easy. Qed.

Definition add (x y : nat) (rel : t) : t :=
  if x =? y then (x, y) :: rel
  else (x, y) :: (y, x) :: rel.

End NatSRel.
