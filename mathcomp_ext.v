From mathcomp Require Export ssreflect ssrbool ssrnat ssrfun
  eqtype fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments val : simpl never.

(* Reflection views *)
Lemma and3PP (P1 P2 P3 : Prop) (b1 b2 b3 : bool) :
  reflect P1 b1 ->
  reflect P2 b2 ->
  reflect P3 b3 ->
  reflect [/\ P1, P2 & P3] [&& b1, b2 & b3].
Proof. move=> H1 H2 H3. by apply: (iffP and3P) => -[/H1? /H2? /H3].
Qed.

(* Finite forall *)
Lemma forall_true (T : finType) :
  [forall x : T, true] = true.
Proof. by apply/forallP. Qed.

Lemma forall_false (T : finType) :
  [forall x : T, false] = (#|T| == 0).
Proof. done. Qed.

Lemma forall_andb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x && Q x] =
  [forall x : T, P x] && [forall x : T, Q x].
Proof. Admitted.

Lemma forall_orb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x || Q x] =
  [forall x : T, P x] || [forall x : T, Q x].
Proof. Admitted.

(* Symmetric relations *)
Definition symb (T : finType) (R : rel T) :=
  [forall x, forall y, R x y == R y x].

Lemma symP (T : finType) (R : rel T) :
  reflect (symmetric R) (symb R).
Proof. by apply: (iffP 'forall_'forall_eqP). Qed.

Definition rel0 (T : Type) := [rel x y : T | false].
Lemma rel0_sym (T : Type) : symmetric (@rel0 T).
Proof. done. Qed.

Definition sym_eq (T : eqType) (p q : (T * T)) : bool :=
  ((p.1 == q.1) && (p.2 == q.2)) || ((p.2 == q.1) && (p.1 == q.2)).
Notation "p =sym= q" := (sym_eq p q)
  (at level 70, no associativity).

(* Finite functions *)
Definition ffcomp (A B C : finType)
  (f : {ffun A -> B}) (g : {ffun B -> C}) : {ffun A -> C} :=
  [ffun x => g (f x)].
Notation "f \c g" := (ffcomp f g)
  (at level 60, right associativity).

Lemma ffcompA (A B C D : finType)
  (f : {ffun A -> B}) (g : {ffun B -> C}) (h : {ffun C -> D}) :
  (f \c g) \c h = f \c g \c h.
Proof. apply/ffunP => a. by rewrite !ffunE. Qed.
