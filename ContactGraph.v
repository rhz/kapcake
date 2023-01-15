From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing Coercions. *)
(* Set Printing Implicit. *)

Module ContactGraphs.

Lemma neqxx (T: eqType) (x : T) : ~(x != x).
Proof. move=> /eqP xNEx. by apply: xNEx. Qed.

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

(* finite maps *)
(* Extra lemmas for finite maps.
 * One of them will be soon integrated into mathcomp.finmap: codomf_cat.
 * codomf_const: codomf of constant map.
 * setksD: setks and domf.
 * setksC: setks and codomf.
 *)
Section FinMap.
Variables (K V : choiceType).

Lemma codomf_cat (f g : {fmap K -> V}) :
  codomf (f + g) = codomf g `|` codomf f.[\domf g].
Proof using Type.
  apply/fsetP => v. rewrite ![RHS]inE.
  apply/codomfP/(orPP (codomfP _ _) (codomfP _ _)); last first.
  - move=> [] [x xI]; exists x; rewrite fnd_cat.
    + by case: fndP xI.
    + move: xI. rewrite fnd_rem. by case: ifP.
  - move=> [] x. rewrite fnd_cat. case: fndP => // [xg gx|xNg fx].
    + left. exists x. by rewrite in_fnd.
    + right. exists x. by rewrite fnd_rem ifN.
Qed.

Definition setks (m : {fmap K -> V}) (ks : {fset K}) (v : V) :=
  m + [fmap _ : ks => v].

Lemma setksD (m : {fmap K -> V}) (ks : {fset K}) (v : V) :
  domf (setks m ks v) = ks `|` domf m.
Proof using Type. by rewrite domf_cat fsetUC. Qed.

Lemma codomf_const (ks : {fset K}) (v : V) :
  ks != fset0 -> codomf [fmap _ : ks => v] = [fset v].
Proof using Type.
  move=> /fset0Pn [k k_in_ks].
  apply/fsetP=> x. rewrite !inE. apply/existsP.
  case: (boolP (x == v)) => [/eqP-> | xNEv] /=.
  - exists [` k_in_ks]. by rewrite ffunE.
  - move=> [x' /eqP H]. rewrite ffunE in H.
    rewrite H in xNEv. by apply: (@neqxx _ x).
Qed.

Lemma setksC (m : {fmap K -> V}) (ks : {fset K}) (v : V) :
  ks != fset0 ->
  codomf (setks m ks v) = v |` codomf m.[\ ks].
Proof using Type.
  move=> H. by rewrite codomf_cat codomf_const.
Qed.

Definition getks (m : {fmap K -> V}) (v : V) : {fset K} :=
  [fset k | k in m & m.[? k] == Some v].

End FinMap.

Section NS.
(* types for nodes and sites *)
Variables (N S : choiceType).

(* contact graphs *)
Record cg : Type :=
  CG { siteMap : {fmap S -> N}
     ; edges : rel S
     ; edges_sym : symmetric edges
    }.

Definition empty : cg := @CG fmap0 _ (@rel0_sym S).

Section CG.
Variable (g : cg).
Definition nodes : {fset N} := codomf (siteMap g).
Definition sites : {fset S} := domf (siteMap g).
Definition sites_of (n : N) : {fset S} := getks (siteMap g) n.

Definition add_site (s : S) (to_n : N) : cg :=
  @CG (siteMap g).[s <- to_n] (edges g) (edges_sym g).

Definition add_node (n : N) (sites : {fset S}) : cg :=
  @CG (setks (siteMap g) sites n) (edges g) (edges_sym g).

Definition add_edge (s t : S) : cg.
  pose es x y := ((x, y) =sym= (s, t)) || (@edges g x y).
  have @es_sym : symmetric es; last first.
    exact: (@CG (siteMap g) es es_sym).
  rewrite /es /eq_sym /symmetric => x y.
  case: ((x == s) && (y == t)). by rewrite [_ || true]orbC.
  case: ((y == s) && (x == t)) => //.
  rewrite !orFb. by apply: (@edges_sym g).
Qed.

Definition remove_site (s : S) : cg :=
  @CG (siteMap g).[~ s] (edges g) (edges_sym g).

Definition remove_sites (ss : {fset S}) : cg :=
  @CG (siteMap g).[\ ss] (edges g) (edges_sym g).

Definition remove_node (n : N) : cg :=
  remove_sites (sites_of n).

Definition remove_edge (s t : S) : cg.
  pose es x y := if (x, y) =sym= (s, t) then false else @edges g x y.
  have @es_sym : symmetric es; last first.
    exact: (@CG (siteMap g) es es_sym).
  rewrite /es /eq_sym /symmetric => x y.
  case: ((x == s) && (y == t)). by rewrite [_ || true]orbC.
  case: ((y == s) && (x == t)) => // /=. by apply: (@edges_sym g).
Qed.

End CG.
End NS.


(* Lemmas for contact graphs.
 * add_nodeN: add_node and nodes.
 * add_nodeS: add_node and sites.
 * remove_nodeN: add_node and nodes.
 * remove_nodeS: add_node and sites.
 *)
Module Lemmata.
Section CG_NS.
Variables (N S : choiceType) (g : cg N S).

Lemma add_nodeN (n : N) (ss : {fset S}) :
  ss != fset0 ->
  nodes (add_node g n ss) = n |` nodes (remove_sites g ss).
Proof using Type. apply: setksC. Qed.

Lemma add_nodeS (n : N) (ss : {fset S}) :
  sites (add_node g n ss) = sites g `|` ss.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

Lemma notin_sites (n1 n2 : N) (s : sites g) :
  (siteMap g s == n1) && (n1 != n2) ->
  fsval s \notin sites_of g n2.
Proof using Type.
Admitted.

Lemma notin_sites' (n : N) (s : sites g) :
  fsval s \notin sites_of g n -> siteMap g s != n.
Proof using Type.
Admitted.

Lemma remove_nodeN (n : N) :
  nodes (remove_node g n) = nodes g `\ n.
Proof using Type.
  rewrite /remove_node /nodes.
  (* rewrite codomf_rem_exists. *)
  rewrite codomf_rem. Locate "\notin".
  Search "fset" "eq_". About Imfset.imfset.
  apply/fsetP => x. apply/imfsetP.
  case: ifP => /=. Locate "exists2".
  (* use x to get the a site of x: *)
  (* if x is in codomf (siteMap g) then there must be a site *)
  (* mapping to it in domf (siteMap g). *)
  Search (_ \in _ `\ _).
  Search (_ \in codomf _). Search "fset" (_ \in _).
  (* rewrite in_fsetD1 => /andP[xNEn xIc]. *)
  (* rewrite in_fsetD1 => /andP[xNEn /codomfP[s Hs]]. *)
  rewrite in_fsetD1 mem_codomf => /andP[xNEn /existsP[s Hs]].
  exists s. Locate "pred". About SimplPred. rewrite inE.
  apply (@notin_sites x n s).
  - by rewrite xNEn Hs.
  - by rewrite (eqP Hs).
  move=> /negbT xNIcod [s sNSOn] sSOx.
  (* the proof proceeds by showing that x == n *)
  rewrite inE in sNSOn.
  Search (_ ?x = _) codomf. About mem_codomf.
  have xIcod: x \in codomf (siteMap g).
  { rewrite mem_codomf. apply/existsP.
    exists s. by rewrite sSOx. }
  rewrite !inE in xNIcod.
  apply/negP: xNIcod. rewrite negbK. apply/andP. split; last first.
  apply/existsP. exists s. by rewrite sSOx.
  (* by sNSOn, siteMap g s != n *)
  (* have H (n1 : N) (s1 : sites g) : *)
  (*   reflect (fsval s1 \in sites_of g n1) (siteMap g s1 == n1). *)
  (* have H (n1 : N) (s1 : sites g) : *)
  (*   fsval s1 \in sites_of g n1 <-> siteMap g s1 == n1. *)
  rewrite sSOx.
  apply: notin_sites'. by apply: sNSOn.
Qed.
  (* suff sID: forall s : S, *)
  (*     s \in sites_of g n -> s \in domf (siteMap g). *)
  (* suff H: forall s : S, forall h : s \in sites_of g n, *)
  (*     siteMap g [` sID s h] = n. *)
  (* suff H1: forall v : N, *)
  (*     [exists k, (val k \notin sites_of g n) && *)
  (*                  (siteMap g k == v)] = *)
  (*       (v != n). *)

Lemma imfset_id' (X : {fset N}) : [fset x | x in X] = X.
Proof using Type. by rewrite imfset_id. Qed.

Search "fset" reflect.

Lemma b (X : {fset N}) (n : N) :
  [fset x | x in X & x != n] = X `\ n.
Proof using Type.
  apply/fsetP => x'. symmetry. About fsetD1P. apply/fsetD1P.
Admitted.

Lemma sites_ofDM (s : S) (n : N) :
  s \in sites_of g n -> s \in domf (siteMap g).
Proof using Type.
Admitted.

Lemma sites_ofM (s : S) (n : N) (H : s \in sites_of g n) :
  siteMap g [` sites_ofDM H] = n.
Proof using Type.
Admitted.

Lemma remove_nodeS (n : N) :
  sites (remove_node g n) = sites g `\` sites_of g n.
Proof using Type.
Admitted.


End CG_NS.
End Lemmata.

End ContactGraphs.
