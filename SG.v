From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.
Set Printing Implicit.

Module SiteGraphs.

Coercion fset_sub_finType : finSet >-> finType.
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

Definition eq_sym (T : eqType) (p1 p2 : (T * T)) : bool :=
  match p1, p2 with
    (x, y), (z, w) => ((x == z) && (y == w)) ||
                      ((y == z) && (x == w)) end.
Notation "p1 =sym= p2" := (eq_sym p1 p2)
  (at level 70, no associativity).

Section SG_NS.
(* types for nodes and sites *)
Variables (N S : choiceType).

(* site graphs *)
Record sg : Type :=
  SG { nodes : {fset N}
     ; siteMap : {fmap S -> nodes}
     ; edges : rel S
     ; edges_sym : symmetric edges
    }.

Definition empty : sg :=
  @SG fset0 fmap0 _ (@rel0_sym S).

Variable (g : sg).
Definition sites : {fset S} := domf (siteMap g).

Definition add_node (n : N) : sg :=
  @SG (n |` nodes g)
    (FinMap (finfun (fincl (fsubsetUr [fset n] (nodes g))
                       \o siteMap g)))
    (@edges g) (@edges_sym g).

Definition add_site (s : S) (to_node : nodes g) : sg :=
  @SG (nodes g) (siteMap g).[s <- to_node]
    (@edges g) (@edges_sym g).

Definition add_edge (s t : S) : sg.
  refine (@SG (nodes g) (siteMap g)
            (fun x y => ((x, y) =sym= (s, t)) || (@edges g x y)) _).
  rewrite /eq_sym /symmetric => x y.
  case: ((x == s) && (y == t)). by rewrite [_ || true]orbC.
  case: ((y == s) && (x == t)) => //.
  rewrite !orFb. by apply: (@edges_sym g).
Qed.

End SG_NS.

End SiteGraphs.
