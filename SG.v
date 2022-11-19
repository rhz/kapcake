From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SiteGraphs.

Local Open Scope fset.
Local Open Scope fmap.

(* symmetric relations *)
Definition symb (T : finType) (R : rel T) :=
  [forall x, forall y, R x y == R y x].

Definition symmetric (T : Type) (R : rel T) :=
  forall x y, R x y == R y x.

Lemma symP (T : finType) (R : rel T) :
  reflect (symmetric R) (symb R).
Proof. by apply: (iffP 'forall_forallP). Qed.

Definition rel0 (T : Type) (_ _ : T) := false.
Lemma rel0_sym (T : Type) : symmetric (@rel0 T).
Proof. done. Qed.
(* Lemma rel0_sym (C : choiceType) (f : {fset C}) : symmetric (@rel0 f). *)
(* Proof. done. Qed. *)
Lemma rel0_symb (T : finType) : symb (@rel0 T).
Proof. by apply/'forall_forallP. Qed.

(* attempt at finding missing coercion *)
Definition g (T : finType) := tt.
Variable (C : choiceType) (f : {fset C}).
Print Graph.
(* Check @rel0_symb f. *)
Set Printing Coercions.
Set Printing Implicit.
Check symb (@rel0 f).
Check g [finType of f].
Check g (@fset_sub_finType C f).
About fset_sub_finType.
Coercion fset_sub_finType : finSet >-> finType.
Check g f.

(* site graphs *)
Record sg (N S : choiceType) : Type :=
  SG { nodes : {fset N}
     ; siteMap : {fmap S -> nodes}
     (* ; sites := domf siteMap (* : {fset S} *) *)
     ; edges : rel S
     ; edges_sym : symmetric edges
    }.

Notation "x -- y" := (edges x y) (at level 30).
Arguments edges : simpl never.
(* Notation sgn := (sg [choiceType of nat] [choiceType of nat]). *)

Section SG_NS.
Variables (N S : choiceType).

Definition empty : sg N S :=
  @SG _ _ fset0 fmap0 _ (@rel0_sym S).

Variable (g : sg N S).

Definition sites := domf (siteMap g). (* : {fset S} *)

Definition add_node (n : N) : sg N S :=
  @SG N S (n |` nodes g)
    (FinMap (finfun (fincl (fsubsetUr [fset n] (nodes g))
                       \o siteMap g)))
    (@edges N S g) (@edges_sym N S g).

Definition add_site (s : S) (to_node : nodes g) : sg N S :=
  @SG N S (nodes g) (siteMap g).[s <- to_node]
    (@edges N S g) (@edges_sym N S g).

End SG_NS.

End SiteGraphs.
