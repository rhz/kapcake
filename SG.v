From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SiteGraphs.

Reserved Notation "x -- y" (at level 30).

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
     ; _ : symmetric edges
    }.

Notation "x -- y" := (edges x y) (at level 30).
Arguments edges : simpl never.
(* Notation sgn := (sg [choiceType of nat] [choiceType of nat]). *)

Section SG_NS.
Variables (N S : choiceType).

Definition empty : sg N S :=
  @SG _ _ fset0 fmap0 _ (relF_sym (domf fmap0)).

Variable (G : sg N S).

Definition add_node (n : N) : sg N S.
  case: G => ns sm ss es es_sym.
  set ns' := (n |` ns)%fset.
  have sm' : {fmap S -> ns'}.
    exists (domf := ss). (* or apply: (@FinMap S ns' ss). *)
    refine [ffun x => _].
    (* Set Printing Coercions. *)
    exists (fsval := val (sm x)).
    (* or apply: (@FSetSub _ _ (val (sm x))) *)
    rewrite in_fsetU.
    apply/orP. right.
    (* Set Printing Coercions. Check sm. Print sg. *)
    by case: (sm x).
  set ss' := domf sm'.
  have es' : rel ss'.
    have ->: ss' = ss.
      case: ss'.
      admit.
    exact: es.
  have es'_sym : symmetric es'.
    admit.
  exact: (@SG _ _ ns' sm' es' es'_sym).
  (* Unset Printing Notations. *)
Defined.

End SG_NS.

End SiteGraphs.
