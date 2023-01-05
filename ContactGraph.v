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
Section FinMap.
Variables (K V : choiceType).

(* Lemma codomf_cat (f g : {fmap K -> V}) : *)
(*   codomf (f + g) = codomf g `|` codomf f.[\domf g]. *)
(* Proof. *)
(* apply/fsetP=> v'; rewrite ![RHS]inE. *)
(* apply/codomfP/orP => [[x /fndSomeP[xI]]|[]]. *)
(* - have [xIg|xNIg] := (boolP (x \in domf g)). *)
(*     by rewrite getf_catr // => <-; left; rewrite in_codomf. *)
(*   rewrite getf_catl // => [|x1 <-]. *)
(*     by rewrite !inE (negPf xNIg) orbF in xI. *)
(*   right. *)
(*   apply/codomfP; exists x. *)
(*   rewrite fnd_rem (negPf xNIg). *)
(*   by apply/fndSomeP; exists x1. *)
(* - move=> /codomfP[x /fndSomeP[xI xM]]. *)
(*   exists x. *)
(*   rewrite fnd_cat xI. *)
(*   by apply/fndSomeP; exists xI. *)
(* move=> /codomfP[x]. *)
(* rewrite fnd_rem. *)
(* case: (boolP (_ \in _)) => // xNIg /fndSomeP[xIm <-]. *)
(* exists x; apply/fndSomeP. *)
(* have xH : x \in domf (f + g) by rewrite inE xIm. *)
(* by exists xH; rewrite getf_catl. *)
(* Qed. *)

Lemma codomf_cat (f g : {fmap K -> V}) :
  codomf (f + g) = codomf g `|` codomf f.[\domf g].
Proof using Type.
  apply/fsetP=> v. rewrite ![RHS]inE.
  apply/codomfP/orP => [[x /fndSomeP[xI]] | []].
  - have [xIg|xNIg] := (boolP (x \in domf g)).
    + About getf_catr. rewrite getf_catr => <-. left.
      About in_codomf. apply: in_codomf.
    + About getf_catl. rewrite getf_catl // => [|x1 <-].
      * Check (negPf xNIg). by rewrite !inE (negPf xNIg) orbF in xI.
      * right. apply/codomfP. exists x.
        About fnd_rem. rewrite fnd_rem (negPf xNIg).
        apply/fndSomeP. by exists x1.
  - move=> /codomfP[x /fndSomeP[xI xM]].
    exists x. About fnd_cat. rewrite fnd_cat xI.
    apply/fndSomeP. exists xI. exact: xM.
  - move=> /codomfP[x]. rewrite fnd_rem.
    case: (boolP (x \in domf g)) => // xNIg /fndSomeP[xIm <-].
    exists x. apply/fndSomeP.
    have xH : x \in domf (f + g) by rewrite inE xIm.
    exists xH. by rewrite getf_catl.
Qed.

(* add many keys pointing to the same value *)
(* Fixpoint setks (m : {fmap K -> V}) (ks : seq K) (v : V) := *)
(*   if ks is k :: ks' then setks m.[k <- v] ks' v else m. *)

(* Definition setks (m : {fmap K -> V}) (ks : {fset K}) (v : V) := *)
(*   [fmap k : ks `|` domf m => *)
(*      if val k \in ks then v *)
(*      else odflt v (fnd m (val k))]. *)

(* Lemma setksD (m : {fmap K -> V}) (ks : {fset K}) (v : V) : *)
(*   domf (setks m ks v) = ks `|` domf m. *)
(* Proof using Type. done. Qed. *)

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

(* Lemma setksC (m : {fmap K -> V}) (ks : {fset K}) (v : V) : *)
(*   ks != fset0 -> *)
(*   codomf (setks m ks v) = v |` codomf m.[\ ks]. *)
(* Proof using Type. *)
(* move=> /fset0Pn [k k_in_ks]; rewrite /setks. *)
(* apply/fsetP=> v'; rewrite ![RHS]inE. *)
(* apply/codomfP/orP => [[x /fndSomeP[xI]]|[]]. *)
(* - have [xIks|xNIks] := (boolP (x \in ks)). *)
(*     by rewrite getf_catr // ffunE => ->; left; rewrite inE. *)
(*   rewrite getf_catl // => [|x1 <-]. *)
(*     by rewrite !inE (negPf xNIks) orbF in xI. *)
(*   right. *)
(*   apply/codomfP; exists x. *)
(*   rewrite fnd_rem (negPf xNIks). *)
(*   by apply/fndSomeP; exists x1. *)
(* - rewrite inE => /eqP->. *)
(*   exists k. *)
(*   rewrite fnd_cat k_in_ks. *)
(*   by apply/fndSomeP; exists k_in_ks; rewrite ffunE. *)
(* move=> /codomfP[x]. *)
(* rewrite fnd_rem. *)
(* case: (boolP (_ \in _)) => // xNIks /fndSomeP[xIm <-]. *)
(* exists x; apply/fndSomeP. *)
(* have xH : x \in domf (m + [fmap _ : ks => v]) by rewrite inE xIm. *)
(* by exists xH; rewrite getf_catl. *)
(* Qed. *)

Lemma setksC (m : {fmap K -> V}) (ks : {fset K}) (v : V) :
  ks != fset0 ->
  codomf (setks m ks v) = v |` codomf m.[\ ks].
Proof using Type.
  move=> H. by rewrite codomf_cat codomf_const /=.
Qed.

(* Proof using Type. *)
(*   move=> /fset0Pn [k k_in_ks]. *)
(*   apply/fsetP=> v'. rewrite !inE. *)
(*   case H: [exists x, setks m ks v x == v']. *)
(*   move: H => /existsP [k' H']. *)
(* Admitted. *)
(**
  case H: [exists x, m.[\ ks] x == v'].
  (* Search [exists ?x, _ x ]. *)
  move: H => /existsP [k' H'].
  suff -> : [exists x, setks m ks v x == v'].
    by rewrite [_ || true]orbC.
  apply/existsP.
  exists k'.

  have [-> | neq_v'v] /= := altP eqP.
  (* v' == v *) apply/existsP.
  have ks_sub : ks `<=` (ks `|` domf m) by rewrite fsubsetUl.
  exists (fincl ks_sub [` k_in_ks]).
  (* set x := fsval (fincl ks_sub [` k_in_ks]) \in ks. *)
  (* cbv in x. *)
  by rewrite ffunE /= k_in_ks.
  (* neq_v'v : v' != v *) apply/existsP.
Admitted.
 *)

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
  remove_sites (getks (siteMap g) n).

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


Module Lemmata.
Section CG_NS.
Variables (N S : choiceType) (g : cg N S).

Lemma nodesN (n : N) (ss : {fset S}) :
  ss != fset0 ->
  nodes (add_node g n ss) = n |` nodes (remove_sites g ss).
Proof using Type.
  rewrite /nodes /add_node /=. apply: setksC.
Qed.

Lemma smN (n : N) (ss : {fset S}) :
  siteMap (add_node g n ss) = siteMap g.
Proof using Type.
Admitted.

End CG_NS.
End Lemmata.

End ContactGraphs.
