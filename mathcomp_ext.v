From mathcomp Require Export ssreflect ssrbool ssrnat ssrfun
  eqtype fintype choice finfun.
From mathcomp Require Import seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments val : simpl never.

(* ssrbool *)
Lemma and3PP (P1 P2 P3 : Prop) (b1 b2 b3 : bool) :
  reflect P1 b1 ->
  reflect P2 b2 ->
  reflect P3 b3 ->
  reflect [/\ P1, P2 & P3] [&& b1, b2 & b3].
Proof. move=> H1 H2 H3. by apply: (iffP and3P) => -[/H1? /H2? /H3].
Qed.

(* symmetric relations *)
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

(* fintype *)
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

(* Variables (T1 T2 : choiceType) (A : {fset T1}). *)
(* Hypothesis (f : A -> {fset T2}). *)
(* Variable i0 : A. *)
(* Check #|`f i0|. *)
(* Check [arg min_(x < i0 in A) #|`f x|]. *)

(* Variant extremum_spec {T : eqType} (ord : rel T) *)
(*   {I : finType} (P : pred I) (F : I -> T) : I -> Type := *)
(*   ExtremumSpec (i : I) of P i & *)
(*     (forall j : I, P j -> ord (F i) (F j)) : *)
(*     extremum_spec ord P F i. *)
Variant extremum_spec {T : eqType} (ord : rel T)
  {I : finType} (P : pred I) (F : I -> T)
  : option I -> Type :=
  | Extremum i of P i & (forall j : I, P j -> ord (F i) (F j))
      : extremum_spec ord P F (Some i)
  | NoExtremum of P =1 xpred0 : extremum_spec ord P F None.
Let arg_pred {T : eqType} ord {I : finType} (P : pred I) (F : I -> T) :=
  [pred i | P i & [forall (j | P j), ord (F i) (F j)]].
Section Extremum.
Variables (T : eqType) (ord : rel T)
  (I : finType) (P : pred I) (F : I -> T).
Definition extremum : option I := pick (arg_pred ord P F).
Hypothesis ord_refl : reflexive ord.
Hypothesis ord_trans : transitive ord.
Hypothesis ord_total : total ord.
(* Lemma extremumP : if extremum is Some e *)
(*                   then extremum_spec ord P F e else True. *)
(* Proof. rewrite /extremum. *)
(*        case: pickP => [i /andP[Pi /'forall_implyP/= min_i] | no_i]. *)
(*        by split=> // j; apply/implyP. done. *)
(* Qed. *)
Lemma extremumP : extremum_spec ord P F extremum.
Proof using ord_refl ord_total ord_trans.
  rewrite /extremum.
  case: pickP => [i /andP[Pi /'forall_implyP xtrm]|].
  constructor => //.
  rewrite /eqfun /= => no_i. constructor.
  rewrite /eqfun => i. apply: negbTE. move/negbT: (no_i i).
  rewrite negb_and => /orP[notPi | /negP noXtm] //.
  apply/negP. move=> Pi.
  have := sort_sorted ord_total [seq F k | k <- enum P].
  set s := sort _ _ => ss.
  have s_gt0 : size s > 0.
  - rewrite size_sort size_map -cardE. apply/card_gt0P. by exists i.
  pose t0 := nth (F i) s 0.
  have: t0 \in s by rewrite mem_nth.
  rewrite mem_sort => /mapP/sig2_eqW[it0].
  rewrite mem_enum => it0P def_t0.
  have /negP[/=] := no_i it0.
  rewrite [P _]it0P/=. apply/'forall_implyP => j Pj.
  have /(nthP (F i))[k g_lt <-] : F j \in s
      by rewrite mem_sort map_f ?mem_enum.
  by rewrite -def_t0 sorted_leq_nth.
Qed.
End Extremum.
Section ArgMinMax.
Variables (I : finType) (P : pred I) (F : I -> nat).
Definition arg_min := extremum leq P F.
Definition arg_max := extremum geq P F.
End ArgMinMax.
Notation "[ 'arg' 'min_' ( i | P ) F ]" :=
  (arg_min (fun i => P%B) (fun i => F))
    (at level 0, i at level 10,
      format "[ 'arg'  'min_' ( i  |  P )  F ]") : nat_scope.
Notation "[ 'arg' 'min_' ( i 'in' A ) F ]" :=
  [arg min_(i | i \in A) F]
    (at level 0, i at level 10,
      format "[ 'arg'  'min_' ( i  'in'  A )  F ]") : nat_scope.
Notation "[ 'arg' 'max_' ( i | P ) F ]" :=
  (arg_max (fun i => P%B) (fun i => F))
    (at level 0, i at level 10,
      format "[ 'arg'  'max_' ( i  |  P )  F ]") : nat_scope.
Notation "[ 'arg' 'max_' ( i 'in' A ) F ]" :=
    [arg max_(i | i \in A) F]
  (at level 0, i at level 10,
   format "[ 'arg'  'max_' ( i  'in'  A )  F ]") : nat_scope.

(* finfun *)
Definition ffcomp (A B C : finType)
  (f : {ffun A -> B}) (g : {ffun B -> C}) : {ffun A -> C} :=
  [ffun x => g (f x)].
Notation "f \c g" := (ffcomp f g)
  (at level 60, right associativity).

Lemma ffcompA (A B C D : finType)
  (f : {ffun A -> B}) (g : {ffun B -> C}) (h : {ffun C -> D}) :
  (f \c g) \c h = f \c g \c h.
Proof. apply/ffunP => a. by rewrite !ffunE. Qed.
