Require Import Program.
From KapCake Require Import finmap_ext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing Coercions. *)
(* Set Printing Implicit. *)
(* Module ContactGraphs. *)

Local Open Scope fset.
Local Open Scope fmap.

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

Section SN.
(* Types for nodes and sites *)
Variables (S N : choiceType).

(* Contact graphs *)
Record cg : Type :=
  CG { siteMap : {fmap S -> N}
     ; edges : rel S
     ; edges_sym : symmetric edges
     (* wildcards *)
     ; wildcards : {fset S}
     ; w_in_sites : wildcards `<=` domf siteMap
    }.

Definition empty : cg := @CG fmap0 _ (@rel0_sym S) fset0 (fsub0set _).

Section CG.
Variable (g : cg).
Definition nodes : {fset N} := codomf (siteMap g).
Definition sites : {fset S} := domf (siteMap g).
Definition sites_of (n : N) : {fset sites} :=
  preimage_of (siteMap g) n.
Definition is_free (s : S) : bool :=
  [forall t : sites, edges g s (val t) == false].

Definition add_sites (m : {fmap S -> N}) : cg :=
  @CG (siteMap g + m) (edges g) (edges_sym g)
    (wildcards g) (fsubset_cat _ (w_in_sites g)).

Definition add_site (n : N) (s : S) : cg :=
  add_sites [fmap].[s <- n].

Definition add_node (n : N) (ss : {fset S}) : cg :=
  add_sites [fmap _ : ss => n].

Program Definition remove_sites (ss : {fset S}) : cg :=
  @CG (siteMap g).[\ ss] (edges g) (edges_sym g)
    (wildcards g `\` ss) _.
Next Obligation.
  apply/fsubsetP => s /fsetDP [sIw sNIss]. rewrite !inE sNIss.
  by move: (fsubsetP (w_in_sites g) _ sIw) => ->.
Qed.

Definition remove_site (s : S) : cg :=
  remove_sites [fset s].

Definition remove_node (n : N) : cg :=
  remove_sites [fsetval s in sites_of n].

Program Definition add_edge (s t : S) : cg :=
  @CG (siteMap g)
    (fun x y => ((x, y) =sym= (s, t)) || (edges g x y)) _
    (wildcards g) (w_in_sites g).
Next Obligation.
  move=> x y. by rewrite [_ && _ || _]orbC (eqP (edges_sym g x y)).
Qed.

Program Definition remove_edge (s t : S) : cg :=
  @CG (siteMap g)
    (fun x y => if (x, y) =sym= (s, t) then false else edges g x y) _
    (wildcards g) (w_in_sites g).
Next Obligation.
  move=> x y. by rewrite [_ && _ || _]orbC (eqP (edges_sym g x y)).
Qed.

End CG.
End SN.

(* Lemmas for contact graphs.
 * add_nodeN: add_node and nodes.
 * add_nodeS: add_node and sites.
 * add_nodeE: add_node and edges.
 * remove_nodeN: add_node and nodes.
 * remove_nodeS: add_node and sites.
 * remove_nodeE: add_node and edges.
 *)
(* Module Lemmata. *)
Section CG_SN.
Variables (S N : choiceType) (g : cg S N).
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
  nodes (add_node g n ss) = nodes g.
Proof using Type.
  move=> /eqP ->. rewrite /add_node /add_sites /nodes /=.
  by rewrite (@fmap_nil S N [fmap _ : fset0 => n]) // catf0.
Qed.

Lemma add_nodeS n ss :
  sites (add_node g n ss) = sites g `|` ss.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

Lemma add_nodeE n ss :
  edges (add_node g n ss) = edges g.
Proof using Type. done. Qed.

Lemma add_sitesN (f : {fmap S -> N}) :
  nodes (add_sites g f) =
    codomf f `|` nodes (remove_sites g (domf f)).
Proof using Type.
  by rewrite /add_sites /remove_sites /nodes /= codomf_cat.
Qed.

Lemma add_sitesS (f : {fmap S -> N}) :
  sites (add_sites g f) = sites g `|` domf f.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

Lemma add_sitesE n (f : {fmap S -> N}) :
  edges (add_sites g f) = edges g.
Proof using Type. done. Qed.

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

Lemma remove_sitesE ss :
  edges (remove_sites g ss) = edges g.
Proof using Type. done. Qed.

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
  by rewrite !inE andbCA andbb.
  (* alternative proof *)
  (* apply/fsetP => s. rewrite !inE. *)
  (* case: (s \in sites g) => // /=. *)
  (* by rewrite andbF. *)
Qed.

Lemma remove_nodeE n :
  edges (remove_node g n) = edges g.
Proof using Type. done. Qed.

Lemma add_edgeN (s t : S) :
  nodes (add_edge g s t) = nodes g.
Proof using Type. done. Qed.

Lemma add_edgeS (s t : S) :
  sites (add_edge g s t) = sites g.
Proof using Type. done. Qed.

Lemma add_edgeE (s t : S) :
  edges (add_edge g s t) =
    (fun x y => ((x, y) =sym= (s, t)) || edges g x y).
Proof using Type. done. Qed.

Lemma remove_edgeN (s t : S) :
  nodes (remove_edge g s t) = nodes g.
Proof using Type. done. Qed.

Lemma remove_edgeS (s t : S) :
  sites (remove_edge g s t) = sites g.
Proof using Type. done. Qed.

Lemma remove_edgeE (s t : S) :
  edges (remove_edge g s t) =
    (fun x y => if (x, y) =sym= (s, t)
                then false else edges g x y).
Proof using Type. done. Qed.

End CG_SN.
(* End Lemmata. *)

Section Realisable.
Variables (S N : choiceType) (g : cg S N).

(* Definition no_self_loop : bool := *)
(*   [forall s : sites g, edges g (val s) (val s) == false]. *)
(* Definition at_most_one_edge_per_site : bool := *)
(*   [forall s : sites g, forall t : sites g, forall t' : sites g, *)
(*       edges g (val s) (val t) && edges g (val s) (val t') *)
(*         ==> (t == t')]. *)

Definition is_realisable : bool :=
  (* no_self_loop && at_most_one_edge_per_site. *)
  (* no self loop *)
  [forall s : sites g, edges g (val s) (val s) == false] &&
  (* at most 1 incident edge per site *)
  [forall s : sites g, forall t : sites g, forall t' : sites g,
      edges g (val s) (val t) && edges g (val s) (val t')
        ==> (t == t')] &&
  (* wildcard sites aren't bound *)
  [forall s : sites g, (val s \in wildcards g) ==>
    [forall t : sites g, edges g (val s) (val t) == false]].

End Realisable.

(* Notations *)
Module SGNotations.

Declare Custom Entry siteMapping.
Notation "[ T | s1 , .. , s2 |]" :=
  (let e := empty [choiceType of T] [choiceType of T]
   in (add_site .. (add_site e (snd s1) (fst s1)) ..
         (snd s2) (fst s2)))
    (at level 0, s1 custom siteMapping, s2 custom siteMapping).
Notation "s -> u" := ((s, u)) (in custom siteMapping at level 2,
                           s constr at level 1, u constr at level 1).

Declare Custom Entry edge.
Notation "[ T | s1 , .. , s2 | e1 , .. , e2 |]" :=
  (let e := empty [choiceType of T] [choiceType of T] in
   let g := (add_site .. (add_site e (snd s1) (fst s1)) ..
               (snd s2) (fst s2))
   in (add_edge .. (add_edge g (fst e1) (snd e1)) ..
         (fst e2) (snd e2)))
    (at level 0, s1 custom siteMapping, s2 custom siteMapping,
      e1 custom edge, e2 custom edge).
Notation "s1 -- s2" := ((s1, s2)) (in custom edge at level 2,
                             s1 constr at level 1,
                             s2 constr at level 1).
End SGNotations.
Import SGNotations.

(* Examples of the above notations. *)
Definition g1 := [nat| 0 -> 0, 1 -> 1 |].
Definition g2 := [nat| 0 -> 0, 1 -> 1 | 0 -- 1 |].

(* Print g1. Print g2. *)
(* why does the next line take forever? *)
(* Compute (sites g1). *)
(* Goal is_realisable g1 == true. *)
(*   by rewrite /is_realisable /= /rel0 eqxx !forall_true. *)
(* Qed. *)

(* End ContactGraphs. *)
