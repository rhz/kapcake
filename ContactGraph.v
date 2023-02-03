From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing Coercions. *)
(* Set Printing Implicit. *)

Module ContactGraphs.

(* Lemma neqxx (T: eqType) (x : T) : ~(x != x). *)
(* Proof. move=> /eqP xNEx. by apply: xNEx. Qed. *)

Coercion fset_sub_finType : finSet >-> finType.
Local Open Scope fset.
Local Open Scope fmap.
Arguments val : simpl never.

(* Symmetric relations *)
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

(* Finite sets *)
Section FinSet.
Variable (T : choiceType).

(* two lemmas from finmap_plus.v in graph-theory/theories/core *)
Lemma fsetDl (A B : {fset T}) k :
  k \in A `\` B -> k \in A.
Proof using Type. by case/fsetDP. Qed.

Lemma in_fsep (A : {fset T}) (P : pred T) (y : T) :
  y \in [fset x | x in A & P x] = (y \in A) && (P y).
Proof using Type.
  apply/imfsetP/andP => /= [[x]|[H1 H2]];
    first by rewrite inE => /andP[H1 H2] ->.
  exists y => //. by rewrite inE H1.
Qed.

Lemma fsetD_negb (X : {fset T}) (P : pred T) :
  [fset x in X | ~~(P x)] = X `\` [fset x in X | P x].
Proof using Type.
  apply/fsetP => x. apply/imfsetP/fsetDP.
  move=> [y H ->]. move: H. rewrite !inE => /andP[H1 H2] //.
  split=> //. rewrite negb_and. apply/orP. by right.
  move=> [xIX xNIfsetP]. exists x => //=. rewrite !inE.
  apply/andP. split=> //. apply/negP => HP. apply/negP: xNIfsetP.
  rewrite negbK in_fsep. apply/andP. by split.
Qed.

(* Lemma in_val (U : {fset T}) (A : {fset U}) (x : T) : *)
(*   x \in val @` A -> exists y : U, val y = x. *)
(* Proof using Type. *)
(*   move/imfsetP => [z zIA zEx]. by exists z. *)
(* Qed. *)

(* Lemma val_in_val (U : {fset T}) (A : {fset U}) (x : U) : *)
(*   val x \in val @` A <-> x \in A. *)
(* Proof using Type. *)
(*   split=> [/imfsetP[y yIA xEy] | H]. *)
(*   by move: (val_inj xEy) => ->. *)
(*   apply/imfsetP. exists x => //. *)
(* Qed. *)

Lemma val_fsubset_in (U X : {fset T}) (A : {fset U}) :
  val @` A `<=` X ->
  forall x : U, x \in A -> val x \in X.
Proof using Type.
  move=> /fsubsetP H x xIA. apply: (H (val x)).
  apply/imfsetP. by exists x.
Qed.

Lemma val_fsubset_notin (U X : {fset T}) (A : {fset U}) :
  ~~ (val @` A `<=` X) ->
  (exists a : U, a \in A /\ val a \notin X).
Proof using Type.
  move=> /fsubsetPn[a /imfsetP[y yIA aEy] aNIX].
  exists y. split=> //. by rewrite -aEy.
Qed.

End FinSet.

(* Finite maps *)
(* Extra lemmas for finite maps.
 * codomf_cat will be soon integrated into mathcomp.finmap.
 * codomf_const: codomf of constant map.
 *)
Section FinMap.
Variables (K V : choiceType).
Implicit Types (f g : {fmap K -> V}) (v : V).

Definition preimage_of f v : {fset (domf f)} :=
  [fset k | k : domf f & f k == v].
Notation "f ^-1 v" := (preimage_of f v)
                        (at level 70, right associativity).

Lemma codomf_cat f g :
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

Lemma codomf_const (ks : {fset K}) v :
  ks != fset0 -> codomf [fmap _ : ks => v] = [fset v].
Proof using Type.
  move=> /fset0Pn [k k_in_ks]. apply/fsetP=> w.
  apply/codomfP/imfsetP. move=> [l /fndSomeP[lf H]].
  exists w => //. by rewrite inE -H ffunE.
  move=> [x /[!inE]/eqP H] ->. exists k. apply/fndSomeP.
  exists k_in_ks. by rewrite H ffunE.
Qed.

Lemma in_codomf_fset f (P : pred K) v :
  v \in [fset f k | k : domf f & P (val k)] =
  [exists k : domf f, (f k == v) && P (val k)].
Proof using Type.
  apply/imfsetP/existsP. move=> [k /[!inE]/andP[_ H1]] /eqP H2.
  exists k. by rewrite eqtype.eq_sym H2 H1.
  (* second part *)
  move=> [k /andP[/eqP H HP]]. exists k. by rewrite !inE HP.
  by rewrite H.
Qed.

End FinMap.

Section NS.
(* Types for nodes and sites *)
Variables (N S : choiceType).

(* Contact graphs *)
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
Definition sites_of (n : N) : {fset sites} := preimage_of (siteMap g) n.

Definition add_sites (m : {fmap S -> N}) : cg :=
  @CG (siteMap g + m) (edges g) (edges_sym g).

Definition add_site (n : N) (s : S) : cg :=
  add_sites [fmap].[s <- n].

Definition add_node (n : N) (ss : {fset S}) : cg :=
  add_sites [fmap _ : ss => n].

Definition remove_sites (ss : {fset S}) : cg :=
  @CG (siteMap g).[\ ss] (edges g) (edges_sym g).

Definition remove_site (s : S) : cg :=
  remove_sites [fset s].

Definition remove_node (n : N) : cg :=
  remove_sites [fsetval s in sites_of n].

Definition add_edge (s t : S) : cg.
  pose es x y := ((x, y) =sym= (s, t)) || (@edges g x y).
  have @es_sym : symmetric es; last first.
    exact: (@CG (siteMap g) es es_sym).
  rewrite /es /eq_sym /symmetric => x y.
  case: ((x == s) && (y == t)). by rewrite [_ || true]orbC.
  case: ((y == s) && (x == t)) => //.
  rewrite !orFb. by apply: (@edges_sym g).
Qed.

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
 * add_nodeE: add_node and edges.
 * remove_nodeN: add_node and nodes.
 * remove_nodeS: add_node and sites.
 * remove_nodeE: add_node and edges.
 *)
Module Lemmata.
Section CG_NS.
Variables (N S : choiceType) (g : cg N S).
Implicit Types (n : N) (ss : {fset S}).

Lemma in_sites_of n (s : sites g) :
  siteMap g s == n <-> s \in sites_of g n.
Proof using Type.
  split. move=> /eqP <-.
  by rewrite !inE eqxx.
  by rewrite !inE.
Qed.

Lemma add_nodeN n ss :
  ss != fset0 ->
  nodes (add_node g n ss) = n |` nodes (remove_sites g ss).
Proof using Type.
  move=> H. by rewrite /nodes codomf_cat codomf_const.
Qed.

Lemma add_nodeN0 n ss :
  ss == fset0 ->
  nodes (add_node g n ss) = nodes (remove_sites g ss).
Proof using Type. Admitted.

Lemma add_nodeS n ss :
  sites (add_node g n ss) = sites g `|` ss.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

Lemma add_sitesN (f : {fmap S -> N}) :
  nodes (add_sites g f) =
    codomf f `|` nodes (remove_sites g (domf f)).
Proof using Type. Admitted.

Lemma add_sitesS (f : {fmap S -> N}) :
  sites (add_sites g f) = sites g `|` domf f.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

Lemma remove_sitesN ss :
  nodes (remove_sites g ss) =
    nodes g `\` [fset n in nodes g | val @` sites_of g n `<=` ss].
Proof using Type.
  rewrite /remove_sites /nodes /= codomf_rem -fsetD_negb.
  symmetry. apply/fsetP => n. apply/imfsetP. case: ifP.
  rewrite (in_codomf_fset _ (fun s => s \notin ss)).
  move=> /existsP[s /andP[H1 H2]].
  (* move/(in_codomf_fset _ (fun s => s \notin ss) _) => [s [H1 H2]]. *)
  exists n => //. rewrite !inE. apply/andP. split.
  apply/existsP. by exists s.
  apply/negP. move/val_fsubset_in => H.
  move: (H s (iffLR (in_sites_of n s) H1)). exact/negP.
  (* second part *)
  move=> /negbT H /= [n' H1 H2].
  (* move: H1. rewrite !inE -H2 => /andP[/existsP[s sSOn'] H3]. *)
  move: H1. rewrite !inE -H2 => /andP[_ H3].
  apply/negP: H. rewrite negbK.
  move: H3. move/val_fsubset_notin => [t [H4 H5]].
  rewrite (in_codomf_fset _ (fun s => s \notin ss)).
  move: (iffRL (in_sites_of n t) H4) => H6.
  apply/existsP. exists t. by apply/andP.
Qed.

Lemma remove_sitesS ss :
  sites (remove_sites g ss) = sites g `\` ss.
Proof using Type.
  apply/fsetP => s.
  rewrite in_fsep /sites /= in_fsetD.
  by rewrite andbC -andbA andbb.
  (* rewrite in_fsep /sites /=. *)
  (* by apply/(andPP idP (fsetDP _ _ _))/fsetDP *)
  (* => [[_ [H sNIss]] | [H sNIss]]; split. *)
Qed.

Lemma remove_nodeN n :
  nodes (remove_node g n) = nodes g `\ n.
Proof using Type.
  rewrite /remove_node /nodes.
  rewrite codomf_rem.
  apply/fsetP => x. apply/imfsetP.
  case: ifP => /=.
  (* use x to get the a site of x: *)
  (* if x is in codomf (siteMap g) then there must be a site *)
  (* mapping to it in domf (siteMap g). *)
  rewrite in_fsetD1 mem_codomf => /andP[xNEn /existsP[s Hs]].
  exists s; last first.
    by rewrite (eqP Hs).
  rewrite !inE. apply/negP. rewrite (eqP Hs).
  by apply/negP: xNEn.
  (* second part *)
  (* x \notin codomf (siteMap g) `\ n -> *)
  (* there's no site y of x that's a site of n. *)
  rewrite !inE /=.
  move=> /negbT xNIcod [s sNSOn] sSOx.
  rewrite !inE /= in sNSOn.
  apply/negP: xNIcod. rewrite negbK. apply/andP. split; last first.
  apply/existsP. exists s. by rewrite sSOx.
  rewrite sSOx. apply: sNSOn.
Qed.

Lemma remove_nodeS n :
  sites (remove_node g n) =
    sites g `\` [fset val s | s in sites_of g n].
Proof using Type.
  apply/fsetP => s.
  by rewrite !inE /= unfold_in topredE andbCA andbb.
  (* alternative proof *)
  (* apply/fsetP => s. rewrite !inE. *)
  (* case: (s \in sites g) => // /=. *)
  (* by rewrite andbF. *)
Qed.

End CG_NS.
End Lemmata.

End ContactGraphs.
