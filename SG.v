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

Definition symmetric (T : finType) (R: rel T) :=
  [forall x, forall y, R x y == R y x].

Definition rel0 (C : choiceType) (F : {fset C}) (_ _ : F) := false.
Lemma rel0_sym (C : choiceType) (F : {fset C}) : symmetric (@rel0 C F).
Proof. apply/forallP => x. by apply/forallP. Qed.

(* site graphs *)

Record sg (N S : choiceType) : Type :=
  SG { nodes : {fset N}
     ; siteMap : {fmap S -> nodes}
     ; sites := domf siteMap (* : {fset S} *)
     ; edges : rel sites
     ; edges_sym : symmetric edges
    }.

Notation "x -- y" := (edges x y) (at level 30).
Arguments edges : simpl never.
(* Notation sgn := (sg [choiceType of nat] [choiceType of nat]). *)

Section SG_NS.
Variables (N S : choiceType).

Definition empty : sg N S :=
  @SG _ _ fset0 fmap0 _ (rel0_sym (domf fmap0)).

Variable (G : sg N S).

Definition add_node (n : N) : sg N S :=
  @SG N S (n |` nodes G)
    (FinMap (finfun (fincl (fsubsetUr [fset n] (nodes G))
                       \o siteMap G)))
    (@edges N S G) (@edges_sym N S G).



End SG_NS.

End SiteGraphs.
