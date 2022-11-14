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

Lemma rel0_sym (R: rel void) : symmetric R.
Proof. by apply/forallP. Qed.

Definition relF (C : choiceType) (F : {fset C}) (_ _ : F) := false.
Lemma relF_sym (C : choiceType) (F : {fset C}) : symmetric (@relF C F).
Proof. apply/forallP => x. by apply/forallP. Qed.


Module FinTypeBased.

(* site graphs *)

Record sg : Type :=
  SG { nodes : finType (* seq_sub is also a potential instance *)
     ; sites : finType
     ; siteMap : {ffun sites -> nodes}
     ; edges : rel sites
     ; _ : symmetric edges
    }.

Definition empty : sg :=
  @SG void_finType void_finType
    (finfun (of_void void)) (of_void _) (rel0_sym _).

Notation "x -- y" := (edges x y) (at level 30).
Arguments edges : simpl never.

End FinTypeBased.


(* Module FinMapBased. *)

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
(* Definition empty : sg nat_choiceType nat_choiceType. *)
(*   refine (@SG _ _ fset0 fmap0 _ _). *)
(*   apply: relF_sym. *)
(* Defined. *)
(* Set Printing Implicit. Print empty. *)

(* some attempts at understanding case analysis on fsets *)
Goal forall (N S : choiceType) (G : sg N S), (nodes G).
  (* move=> N S G. exact: (nodes G). *)
  move=> N S.
  case=> ns sm ss es es_sym.
  (* case: ns. *)
  case: (enum_fset ns) => [| n ns' ].
  - (* exact: fset0. *) admit.
  - exists n.
Admitted.

Goal forall (K V : choiceType) (VS : {fset V})
            (f : {fmap K -> VS}) (x : domf f),
    f x \in codomf f.
  move=> K V VS f x. case: (f x).
Admitted.

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
