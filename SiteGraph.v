(* From Coq Require Import Lists.List. *)
(* Import ListNotations. *)
From Coq Require Import Bool.Bool.
(* From Coq Require Import Arith.Arith. *)
(* From Coq Require Import MSets. *)
From KapCake Require Import Rel.
From KapCake Require Import NatMap.
Import NatMap.PartialMapNotation.
From KapCake Require Import NatSet.
From KapCake Require Import Tactics.
From RecordUpdate Require Import RecordSet.
(* Import RecordSetNotations. *)

(***** Site graphs *****)

(* A site graph G consists of
   a finite set of agents A_G,
   a finite set of sites S_G,
   a map σ_G : S_G -> A_G that assigns sites to agents and
   a symmetric edge relation E_G on S_G .
 *)
Record SG : Type :=
  mkSG
    { nodes : NatSet.t
    ; sites : NatSet.t
    ; siteMap : NatMap.partial nat
    ; edges : Rel.t nat
    }.
#[export] Instance etaSG : Settable _ :=
  settable! mkSG <nodes; sites; siteMap; edges>.

Definition SG_to_NatSetMap (sg : SG) : NatSetMap.t :=
  {| NatSetMap.dom := sites sg
  ;  NatSetMap.cod := nodes sg
  ;  NatSetMap.map := siteMap sg |}.
Coercion SG_to_NatSetMap : SG >-> NatSetMap.t.

Definition SG_to_NatSetRel (sg : SG) : NatSetRel.t :=
  {| NatSetRel.over := sites sg
  ;  NatSetRel.rel := edges sg |}.
Coercion SG_to_NatSetRel : SG >-> NatSetRel.t.

Create HintDb site_graphs.

(* Here we are representing the edge relation E_G as
   a list of pairs of nats and we prove for each
   concrete site graph that all pairs are in S_G
   and that the relation is symmetric.

   Also, in this representation we chose a partial map
   from `nat` to `nat` (`NatMap.partial nat`) to represent a
   total map from S_G to A_G since S_G and A_G are not Sets in Coq.
   For each concrete site graph we can prove that the partial map
   is indeed total and its image is indeed in A_G.

   These 3 properties are guaranteed in the mathematical
   representation but not in the computational one.
   When the computational representation of a site graph `g`
   satisfies these 3 properties, we say that `g` is proper.
 *)
Definition is_proper (g: SG) : Prop :=
  NatSetMap.is_total g /\
  NatSetRel.in_dom g /\
  Rel.is_symmetric (edges g).

#[export]
Hint Unfold is_proper NatSetMap.is_total
  NatSetRel.in_dom Rel.is_symmetric : site_graphs.

(* We define the empty site graph that has
   no nodes, no sites, and no edges. *)
Definition empty :=
  {| nodes := NatSet.empty
  ;  sites := NatSet.empty
  ;  siteMap := NatMap.empty
  ;  edges := Rel.empty
  |}.

(* And we prove that the empty site graph
   satisfies the 3 properties above.
 *)
Lemma empty_siteMap_is_total : NatSetMap.is_total empty.
Proof. exact NatSetMap.empty_is_total. Qed.

Lemma empty_edges_in_dom : NatSetRel.in_dom empty.
Proof. cbn. exact NatSetRel.empty_in_dom. Qed.

Lemma empty_edges_is_symmetric : Rel.is_symmetric (edges empty).
Proof. cbn. exact Rel.empty_is_symmetric. Qed.

Corollary empty_is_proper : is_proper empty.
Proof. splits.
       - apply empty_siteMap_is_total.
       - apply empty_edges_in_dom.
       - apply empty_edges_is_symmetric.
Qed.

(* We have some functions to grow site graphs.
   First, a function to add a node `u` to a site graph `g`.
 *)
Definition addNode u (g: SG) : SG :=
  set nodes (fun us => NatSet.add u us) g.

(* Second, a function to add a site `s` to a node `u`
   in a site graph `g`. *)
Definition addSite s toNode g :=
  set siteMap (fun sm => s |-> toNode ; sm)
    (set sites (fun ss => NatSet.add s ss) g).

(* And third, a function to add an edge
   between sites `s1` and `s2` in site graph `g`. *)
Definition addEdge s1 s2 g :=
  set edges (fun es => if s1 =? s2 then (s1, s1) :: es
                       else (s2, s1) :: (s1, s2) :: es) g.

(* Now we prove that these operations
   preserve the 3 properties above. *)
Lemma addNode_pres_siteMap_is_total : forall u g,
    siteMap_is_total g -> siteMap_is_total (addNode u g).
Proof.
  unfold siteMap_is_total. cbn. intros u g H s sInG.
  destruct (H s sInG) as [u' [H1 H2]].
  exists u'. split. D.fsetdec. apply H2.
Qed.

Lemma addSite_pres_siteMap_is_total : forall s u g,
    NatSet.In u (nodes g) ->
    siteMap_is_total g ->
    siteMap_is_total (addSite s u g).
Proof.
  unfold siteMap_is_total. cbn. intros s u g uInG H s1 s1InG.
  destruct (eqbP s s1) as [eq_ss1 | neq_ss1].
  - exists u. split.
    + apply uInG.
    + rewrite eq_ss1. apply NatMap.update_eq.
  - destruct (H s1) as [u' [H1 H2]].
    + apply (D.F.add_3 neq_ss1). apply s1InG.
    + exists u'. split.
      * apply H1.
      * rewrite NatMap.update_neq. apply H2. apply neq_ss1.
Qed.

Lemma addEdge_pres_siteMap_is_total : forall s1 s2 g,
    siteMap_is_total g -> siteMap_is_total (addEdge s1 s2 g).
Proof.
  unfold siteMap_is_total. cbn. intros _ _ g H s sInG.
  destruct (H s sInG) as [u' [H1 H2]].
  exists u'. split. apply H1. apply H2.
Qed.

Lemma addNode_pres_edges_is_symmetric : forall u g,
    edges_is_symmetric g -> edges_is_symmetric (addNode u g).
Proof. unfold edges_is_symmetric. intros u g H s1 s2. cbn. apply H.
Qed.

Lemma addSite_pres_edges_is_symmetric : forall s u g,
    edges_is_symmetric g -> edges_is_symmetric (addSite s u g).
Proof. unfold edges_is_symmetric. intros s u g H s1 s2. cbn. apply H.
Qed.

Lemma addEdge_pres_edges_is_symmetric : forall s1 s2 g,
    edges_is_symmetric g -> edges_is_symmetric (addEdge s1 s2 g).
Proof.
  unfold edges_is_symmetric. intros s1 s2 g H s3 s4. cbn.
  destruct (eqbP s1 s2) as [eq_s1s2 | neq_s1s2].
  - cbn. intros [H1|H2].
    + left. inversion H1. reflexivity.
    + right. apply H. apply H2.
  - cbn. intros [H1|[H2|H3]].
    + right. left. inversion H1. reflexivity.
    + left. inversion H2. reflexivity.
    + right. right. apply H. apply H3.
Qed.

(* Notations *)
Module SGNotations.
Notation "[| u , .. , v |]" :=
  (addNode v .. (addNode u empty) ..)
    (at level 0).

Declare Custom Entry siteMapping.
Notation "[| u , .. , v | s1 , .. , s2 |]" :=
  (let g := (addNode v .. (addNode u empty) ..) in
   (addSite (fst s2) (snd s2) .. (addSite (fst s1) (snd s2) g) ..))
    (at level 0, s1 custom siteMapping, s2 custom siteMapping).
Notation "s -> u" := ((s, u)) (in custom siteMapping at level 2,
                           s constr at level 1, u constr at level 1).

Declare Custom Entry edge.
Notation "[| u , .. , v | s1 , .. , s2 | e1 , .. , e2 |]" :=
  (let g1 := (addNode v .. (addNode u empty) ..) in
   let g2 := (addSite (fst s2) (snd s2) ..
                (addSite (fst s1) (snd s2) g1) ..)
   in (addEdge (fst e2) (snd e2) .. (addEdge (fst e1) (snd e1) g2) ..))
        (at level 0, s1 custom siteMapping, s2 custom siteMapping,
          e1 custom edge, e2 custom edge).
Notation "s1 -- s2" := ((s1, s2)) (in custom edge at level 2,
                             s1 constr at level 1, s2 constr at level 1).
End SGNotations.
Import SGNotations.

(* Example uses of the above notations. *)
Definition g1 := [| 0, 1 |].
Definition g2 := [| 0, 1 | 0 -> 0, 1 -> 1 |].
Definition g3 := [| 0, 1 | 0 -> 0, 1 -> 1 | 0 -- 1 |].

(* One says site graph `g` is realisable iff
   (i) no site has an edge to itself and
   (ii) sites have at most one incident edge.
 *)
Definition noLoop (g: SG) : Prop :=
  forall x y, In (x, y) (edges g) -> x <> y.

Definition atMost1IncidentEdge (g: SG) : Prop := forall x x' y,
    In (x , y) (edges g) ->
    In (x', y) (edges g) -> x = x'.

Definition is_realisable (g: SG) : Prop :=
  noLoop g /\ atMost1IncidentEdge g /\ is_proper g.

#[export]
Hint Unfold is_realisable noLoop atMost1IncidentEdge : site_graphs.

Ltac node_exists :=
  match goal with |- exists u, _ /\ Some ?x = Some u =>
   exists x end.

Tactic Notation "auto_smit" hyp(H) :=
  simpl in H; rewrite ?D.F.add_iff in H; rewrite D.F.empty_iff in H;
  branches H; solve [ substs; cbn; node_exists; split;
                      rewrite ?D.F.add_iff; auto;
                      reflexivity
                    | false ].

(* As an example, we show that `g3` is realisable. *)
Example g3_is_realisable : is_realisable g3.
Proof.
  autounfold with site_graphs. splits.
  - introv H. pairsInList H then_ discriminate.
  - introv H1 H2. pairsInList H1, H2 then_ reflexivity.
  - introv H. cbn. pairsInList H then_ auto.
  - introv H. cbn. auto_smit H.
Qed.
