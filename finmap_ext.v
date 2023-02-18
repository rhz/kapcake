From KapCake Require Export mathcomp_ext.
(* TODO: why is eqtype needed on the next line when it should *)
(* have been exported by the previous line? *)
From mathcomp Require Export eqtype choice ssrfun finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset.
Local Open Scope fmap.

Coercion fset_sub_finType : finSet >-> finType.

(* Finite sets *)
Section FinSet.
Variable (T : choiceType).
Implicit Types (A B C : {fset T}) (x : T).

(* two lemmas from finmap_plus.v in graph-theory/theories/core *)
Lemma fsetDl A B x :
  x \in A `\` B -> x \in A.
Proof using Type. by case/fsetDP. Qed.

Lemma in_fsep A (P : pred T) x :
  x \in [fset y | y in A & P y] = (x \in A) && (P x).
Proof using Type.
  apply/imfsetP/andP => /= [[y]|[H1 H2]];
    first by rewrite inE => /andP[H1 H2] ->.
  exists x => //. by rewrite inE H1.
Qed.

Lemma fsetD_negb A (P : pred T) :
  [fset x in A | ~~(P x)] = A `\` [fset x in A | P x].
Proof using Type.
  apply/fsetP => x. apply/imfsetP/fsetDP.
  move=> [y H ->]. move: H. rewrite !inE => /andP[H1 H2] //.
  split=> //. rewrite negb_and. apply/orP. by right.
  move=> [xIX xNIfsetP]. exists x => //=. rewrite !inE.
  apply/andP. split=> //. apply/negP => HP. apply/negP: xNIfsetP.
  rewrite negbK in_fsep. apply/andP. by split.
Qed.

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

Lemma fset_eq_in A B (AEB : A = B) x : (x \in A) = (x \in B).
Proof using Type.
  move/eqP: AEB. rewrite eqEfsubset => /andP[AIB BIA].
  apply/idP/idP; by apply: fsubsetP.
Qed.

Lemma fset_eq_inl A B (AEB : A = B) x : (x \in A) -> (x \in B).
Proof using Type.
  move/eqP: AEB. rewrite eqEfsubset => /andP[AIB BIA].
  by apply: fsubsetP.
Qed.

Lemma fset_eq_inr A B (AEB : A = B) x : (x \in B) -> (x \in A).
Proof using Type.
  move/eqP: AEB. rewrite eqEfsubset => /andP[AIB BIA].
  by apply: fsubsetP.
Qed.

Lemma fsubset_trans B A C :
  A `<=` B -> B `<=` C -> A `<=` C.
Proof using Type.
  move=> /fsubsetP AsubB /fsubsetP BsubC.
  apply/fsubsetP => x xIA. apply: BsubC. by apply: AsubB.
Qed.

Lemma eq_fsubsetLR A B : A = B -> A `<=` B.
Proof. move/eqP. by rewrite eqEfsubset => /andP[H _]. Qed.

Lemma eq_fsubsetRL A B : A = B -> B `<=` A.
Proof. move/eqP. by rewrite eqEfsubset => /andP[_ H]. Qed.

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
  exists k. by rewrite eq_sym H2 H1.
  (* second part *)
  move=> [k /andP[/eqP H HP]]. exists k. by rewrite !inE HP.
  by rewrite H.
Qed.

Lemma fsubset_cat (A : {fset K}) f g :
  A `<=` domf f -> A `<=` domf (f + g).
Proof using Type.
  move=> /fsubsetP Asub_domf. apply/fsubsetP => k kIA.
  move: (Asub_domf k kIA) => kIdomf.
  by rewrite !inE kIdomf.
Qed.

(* Lemma fmapE' f g (k : domf f) : *)
(*   f = g -> exists (kg : val k \in domf g), f k = g.[kg]. *)
(* Proof using Type. Admitted. *)
(* Lemma fmapE f g (k : domf f) (fdomIgdom : domf f `<=` domf g) : *)
(*   f = g -> f k = g (fincl fdomIgdom k). *)
(* Proof using Type. Admitted. *)

(* Lemma Some_fnd_eq f (A : {fset K}) (k : A) (AEfdom : A = domf f) : *)
(*   f.[? val k] = Some (f.[fset_eq_inl AEfdom (fsvalP k)]). *)
(* Proof using Type. Admitted. *)

(* Lemma imeq f (A : {fset K}) (H : A = domf f) (k : A) : *)
(*   f.[fset_eq_inl H (fsvalP k)] \in codomf f. *)
(* Proof using Type. Admitted. *)

(* Similar to in_codomf but it works on `k \in domf f` *)
(* instead of a value of type `domf f`. *)
Lemma im f (k : K) (kId : k \in domf f) : f.[kId] \in codomf f.
Proof using Type. by apply: in_codomf. Qed.

End FinMap.
Section Composition.
Variables (K V1 V2 : choiceType)
  (f : {fmap K -> V1}) (g : {fmap V1 -> V2})
  (fcodIgdom : codomf f `<=` domf g).

Definition fcomp : {fmap K -> V2} :=
  [fmap x : domf f =>
     g.[fsubsetP fcodIgdom _ (in_codomf x)]].
     (* val [`(in_codomf [`fsubsetP fcodIgdom _ (in_codomf x)])]]. *)

Lemma fcomp_domf : domf fcomp = domf f.
Proof using Type. done. Qed.

Lemma fcompEfg (k : K) (kIf : k \in domf f) (fkIg : f.[kIf] \in g) :
  fcomp.[kIf] = g.[fkIg].
Proof using Type. rewrite ffunE. apply: eq_getf. Qed.

Lemma fcomp_codomf : codomf fcomp `<=` codomf g.
Proof using Type.
  apply/fsubsetP => v2. move/codomfP => [k /fndSomeP[kIf fckEv2]].
  rewrite -fckEv2 ffunE. apply: in_codomf.
Qed.

End Composition.
Section CompositionOf2.
Variables (K V1 V2 : choiceType)
  (f : {fmap K -> V1}) (g : {fmap V1 -> V2})
  (fcodIgdom : codomf f `<=` domf g)
  (f' : {fmap K -> V1})
  (f'codIgdom : codomf f' `<=` domf g).

(* Lemma fcompE1 : f = f' -> fcomp fcodIgdom = fcomp f'codIgdom. *)

End CompositionOf2.
Section CompositionOf3.
Variables (K V1 V2 V3 : choiceType)
  (f : {fmap K -> V1}) (g : {fmap V1 -> V2}) (h : {fmap V2 -> V3})
  (fcodIgdom : codomf f `<=` domf g)
  (gcodIhdom : codomf g `<=` domf h)
  (fgcodIhdom : codomf (fcomp fcodIgdom) `<=` domf h)
  (fcodIghdom : codomf f `<=` domf (fcomp gcodIhdom)).

Lemma fcompA : @fcomp K V1 V3 f (fcomp gcodIhdom) fcodIghdom =
               @fcomp K V2 V3 (fcomp fcodIgdom) h fgcodIhdom.
Proof using Type.
  apply/fmapP => k /=. rewrite /fnd /omap /obind /oapp.
  case: fndP => kf //. rewrite ffunE /=.
Admitted.

Lemma fcompAx (x : domf f) :
  @fcomp K V1 V3 f (fcomp gcodIhdom) fcodIghdom x =
  @fcomp K V2 V3 (fcomp fcodIgdom) h fgcodIhdom x.
Proof using Type. Admitted.

End CompositionOf3.
