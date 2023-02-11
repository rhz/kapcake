From KapCake Require Export mathcomp_ext.
From mathcomp Require Export choice ssrfun finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

Coercion fset_sub_finType : finSet >-> finType.
Arguments val : simpl never.

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
