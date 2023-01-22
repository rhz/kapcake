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

Definition getks (m : {fmap K -> V}) (v : V) : {fset (domf m)} :=
  [fset k | k : domf m & m k == v].

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
Definition sites_of (n : N) : {fset sites} := getks (siteMap g) n.

Definition add_sites (n : N) (ss : {fset S}) : cg :=
  @CG (setks (siteMap g) ss n) (edges g) (edges_sym g).

Definition add_site (n : N) (s : S) : cg :=
  add_sites n [fset s].

Definition add_node (n : N) (ss : {fset S}) : cg :=
  add_sites n ss.

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
 * remove_nodeN: add_node and nodes.
 * remove_nodeS: add_node and sites.
 *)
Module Lemmata.
Section CG_NS.
Variables (N S : choiceType) (g : cg N S).

Lemma add_sitesN (n : N) (ss : {fset S}) :
  ss != fset0 ->
  nodes (add_sites g n ss) = n |` nodes (remove_sites g ss).
Proof using Type. apply: setksC. Qed.

Lemma add_sitesS (n : N) (ss : {fset S}) :
  sites (add_sites g n ss) = sites g `|` ss.
Proof using Type. by rewrite /sites /= fsetUDr fsetDv fsetD0. Qed.

(* Lemma fset_negb_exists (C D : choiceType) *)
(*   (X : {fset C}) (Y : {fset D}) (P : C -> D -> bool) : *)
(*   [fset x in X | ~~[exists y : Y, P x (val y)]] = *)
(*     [fset x in X | [forall y : Y, ~~(P x (val y))]]. *)
(* Proof using Type. Admitted. *)

(* Lemma fsetD_negb (C : choiceType) (X : {fset C}) (P : C -> bool) : *)
(*   [fset x in X | ~~(P x)] = X `\` [fset x in X | P x]. *)
(* Proof using Type. Admitted. *)

(* Lemma fset_binary_exists (C D : choiceType) *)
(*   (X : {fset C}) (Y : {fset D}) (P : C -> D -> bool) : *)
(*   [fset x | x in X, y in Y & P x y] = *)
(*     [fset x in X | [forall y : Y, P x (val y)]]. *)
(* Proof using Type. Admitted. *)

(* Lemma in_codomf_rem (K V : choiceType) (m : {fmap K -> V}) *)
(*   (ks : {fset K}) (v : V) : *)
(*   v \in codomf m.[\ ks] -> v \in codomf m. *)
(* Proof. Admitted. *)

Arguments val : simpl never.

Lemma remove_sitesN (ss : {fset S}) :
  nodes (remove_sites g ss) =
    nodes g `\` [fset n in nodes g | val @` sites_of g n `<=` ss].
Proof using Type.
  (* rewrite /remove_sites /nodes /=. *)
  (* rewrite /restrictf. *)
  (* suff codomf_filterf (K V : choiceType) (m : {fmap K -> V}) *)
  (*   (P : pred K) : *)
  (*   codomf (filterf m P) = [fset m k | k : domf m & P (val k)]. *)
  (* rewrite codomf_filterf. *)

  rewrite /remove_sites /nodes /=.
  rewrite codomf_rem.
  have ->: nodes g `\`
    [fset n in nodes g | val @` sites_of g n `<=` ss] =
    [fset n in nodes g | ~~(val @` sites_of g n `<=` ss)] by admit.
  have in_codomf_cond (m : {fmap S -> N}) (P : pred S) (n' : N) :
    n' \in [fset m s | s : domf m & P (val s)] <->
    exists s : domf m, m s == n' /\ P (val s) by admit.
  have b (n' : N) : forall s : sites g,
      siteMap g s == n' <-> s \in sites_of g n' by admit.
  symmetry. apply/fsetP => n. apply/imfsetP. case: ifP.
  move/(in_codomf_cond (siteMap g) (fun s => s \notin ss))
      => [s [H1 H2]]. (* {in_codomf_cond}. *)
  exists n => //. rewrite !inE. apply/andP. split.
  apply/existsP. by exists s.
  apply/negP.
  have a : val @` sites_of g n `<=` ss ->
           (forall s : sites g,
               s \in sites_of g n -> val s \in ss) by admit.
  move/a => H.
  move: (H s (iffLR (b n s) H1)). exact/negP.
  (* second part *)
  move=> /negbT H /= [n' H1 H2].
  (* move: H1. rewrite !inE -H2 => /andP[/existsP[s sSOn'] H3]. *)
  move: H1. rewrite !inE -H2 => /andP[_ H3].
  apply/negP: H. rewrite negbK.
  have c : ~~ (val @` sites_of g n `<=` ss) ->
           (exists s : sites g,
               s \in sites_of g n /\ val s \notin ss) by admit.
  move: H3. move/c => [t [H4 H5]] {c}.
  rewrite (in_codomf_cond (siteMap g) (fun s => s \notin ss)).
  move=> {in_codomf_cond}. move: (iffRL (b n t) H4) => H6.
  by exists t.
Admitted.

(*   rewrite /remove_sites /nodes /=. *)
(*   rewrite codomf_rem. *)
(*   apply/fsetP => n. *)
(*   apply/imfsetP. *)
(*   case: ifP => /=. *)
(*   Search "fset" "D". *)
(*   (* move=> /fsetDP[H1 H2]. *) *)
(*   rewrite in_fsetD mem_codomf. *)
(*   rewrite !inE. rewrite negb_and. *)
(*   move=> /andP[/orP[H|H] /existsP[s Hs]]. *)
(*   exfalso. apply: (negP H). apply/existsP. by exists s. *)
(*   exists s; last first. by rewrite (eqP Hs). *)
(*   rewrite inE. apply/negP=> sIss. apply: (negP H). *)
(*   rewrite /sites_of /getks {H}. Search "fset" (_ `<=` _). *)
(*   Locate "`<=`". Print fsubset. Search "fset" "I". *)
(*   suff in_sub (C : choiceType) (A B : {fset C}) : *)
(*     reflect (forall x, (x \in A) -> (x \in B)) (A `<=` B). *)
(*   apply/in_sub => t H1 {in_sub}. *)

(*   apply/fsetIidPl. *)
(*   apply/fsetP => t. *)
(*   apply/fsetIP/idP. *)
(*   move=> [H1 H2]. exact: H1. *)
(*   move=> H1. split. exact: H1. *)
(* Admitted. *)

Lemma remove_sitesN (ss : {fset S}) :
  ss != fset0 ->
  nodes (remove_sites g ss) =
    [fset n in nodes g |
      [forall s : ss, (siteMap g).[? val s] != Some n]].
(*  ~~[exists s : ss, (siteMap g).[? val s] == Some n]]. *)
Proof using Type.
  move=> /fset0Pn[s sIss].
  (* pose f x y := (siteMap g).[? y] == Some x. *)
  (* rewrite (fset_negb_exists (nodes g) ss f). *)
  (* rewrite fsetD_negb. *)
  (* rewrite fset_binary_exists. *)
  (* pose f x y := (siteMap g).[? y] == Some x. *)
  (* rewrite -(fset_negb_exists (nodes g) ss f). *)
  rewrite /remove_sites /nodes /=. symmetry.
  apply/fsetP => n. apply/imfsetP.
  case: ifP => /=.
  move/[dup]/in_codomf_rem/[swap] => nIc.
  rewrite mem_codomf => /existsP[t Ht].
  exists n => //. rewrite !inE. (* sIss. *)
  apply/andP. split.
  apply/existsP. by exists t.
  apply/forallP => u.
  move: nIc. rewrite mem_codomf => /existsP[v Hv].
  rewrite codomf_rem_exists in nIc.
Admitted.

Lemma remove_nodeN (n : N) :
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

Lemma remove_nodeS (n : N) :
  sites (remove_node g n) =
    sites g `\` [fset val s | s in sites_of g n].
Proof using Type.
  apply/fsetP => s.
  by rewrite !inE /= unfold_in topredE andbCA andbb.
  (* apply/fsetP => s. rewrite !inE. *)
  (* case: (s \in sites g) => // /=. *)
  (* by rewrite andbF. *)
Qed.

End CG_NS.
End Lemmata.

End ContactGraphs.
