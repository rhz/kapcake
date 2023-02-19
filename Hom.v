Require Import Program.
From KapCake Require Import finmap_ext ContactGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

Section NS.
(* Types for nodes and sites *)
Variables (N S : choiceType).

(***** Homomorphisms *****)

(* A homomorphism h : G -> G' of
   site graphs is a pair of total functions,
   h_S : S_G -> S_G' and h_A : A_G -> A_G',
   such that for all s,s' ∈ S_G we have
   (i) h_A(σ_G(s)) = σ_G'(h_S(s)) and
   (ii) if s E_G s0 then h_S(s) E_G' h_S(s').
 *)
Record hom : Type :=
  Hom { dom : cg N S
      ; cod : cg N S
      ; f_sites : {fmap S -> S}
      ; f_nodes : {fmap N -> N}
      ; f_sites_total : sites dom = domf f_sites
      ; f_nodes_total : nodes dom = domf f_nodes
      ; f_sites_in_cod : codomf f_sites `<=` sites cod
      ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod
      ; sf (s : sites dom) := fset_eq_inl f_sites_total (fsvalP s)
      ; nf (n : nodes dom) := fset_eq_inl f_nodes_total (fsvalP n)
      ; fs (s : S) (sIc : s \in codomf f_sites) :=
          fsubsetP f_sites_in_cod _ sIc
      ; fn (n : N) (nIc : n \in codomf f_nodes) :=
          fsubsetP f_nodes_in_cod _ nIc
      ; smfn := @fcomp S N N (siteMap dom) f_nodes
                  (eq_fsubsetLR f_nodes_total)
      ; fssm := @fcomp S S N f_sites (siteMap cod) f_sites_in_cod
      ; comm : smfn = fssm
      ; edge_pres :
        [forall s : sites dom, forall t : sites dom,
            edges dom (val s) (val t) ==
              edges cod (f_sites.[sf s]) (f_sites.[sf t])]
    }.
(* proposal for alternative names for fields: *)
(* f_nodes = fn *)
(* f_sites = fs *)
(* f_nodes_total = fnT or fn_total *)
(* f_sites_total = fsT or fs_total *)
(* f_nodes_in_cod = fnIcod *)
(* f_sites_in_cod = fsIcod *)

Lemma f_sites_totalP (h : hom) (s : sites (dom h)) :
  [exists t : sites (cod h),
      (f_sites h).[? val s] == Some (val t)].
Proof using Type.
  apply/existsP. exists [`fs (im (sf s))].
  by rewrite Some_fnd.
Qed.

Lemma f_nodes_totalP (h : hom) (n : nodes (dom h)) :
  [exists m : nodes (cod h),
      (f_nodes h).[? val n] == Some (val m)].
Proof using Type.
  apply/existsP. exists [`fn (im (nf n))].
  by rewrite Some_fnd.
Qed.

Section ContactMap.
Variable (h : hom).

Definition is_contact_map : bool :=
  (* if (dom h) is realisable *)
  is_realisable (dom h) &&
  (* node-local injectivity on sites? *)
  (* ie whenever f_sites s = f_sites t and *)
  (* siteMap (dom h) s = siteMap (dom h) t, then s = t *)
  [forall s : sites (dom h), forall t : sites (dom h),
      ((f_sites h).[sf s] == (f_sites h).[sf t]) &&
      (siteMap (dom h) s == siteMap (dom h) t)
        ==> (s == t)].

End ContactMap.

Section Composition.
Variables (h h' : hom)
  (codEdom : cod h = dom h').

Program Definition comp : hom :=
  {| dom := dom h
  ;  cod := cod h'
  ;  f_sites := @fcomp S S S (f_sites h) (f_sites h') _
  ;  f_nodes := @fcomp N N N (f_nodes h) (f_nodes h') _
  ;  f_sites_total := f_sites_total h
  ;  f_nodes_total := f_nodes_total h
  ;  f_sites_in_cod := _
  ;  f_nodes_in_cod := _
  ;  comm := _
  ;  edge_pres := _
  |}.
Next Obligation. (* codomf (f_sites h) `<=` domf (f_sites h') *)
  rewrite -(f_sites_total h') -codEdom.
  by apply: (f_sites_in_cod h). Qed.
Next Obligation. (* codomf (f_nodes h) `<=` domf (f_nodes h') *)
  rewrite -(f_nodes_total h') -codEdom.
  by apply: (f_nodes_in_cod h). Qed.
Next Obligation. (* f_sites_total *)
  apply: fsubset_trans. apply: fcomp_codomf.
  apply: (f_sites_in_cod h'). Qed.
Next Obligation. (* f_nodes_total *)
  apply: fsubset_trans. apply: fcomp_codomf.
  apply: (f_nodes_in_cod h'). Qed.
Next Obligation. (* comm *)
  apply/fmapP => s.
  set cf_sites := fcomp comp_obligation_1.
  set cf_nodes := fcomp comp_obligation_2.
  set cfssm := @fcomp S S N cf_sites (siteMap (cod h'))
                 comp_obligation_3.
  set csmfn := @fcomp S N N (siteMap (dom h)) cf_nodes
                 (eq_fsubsetLR (f_nodes_total h)).
  have c1Idfn : codomf (fssm h) `<=` domf (f_nodes h').
  - apply: fsubset_trans. apply: fcomp_codomf.
    rewrite codEdom. by apply: (eq_fsubsetLR (f_nodes_total h')).
  set steps := @fcomp S N N (fssm h) (f_nodes h') c1Idfn.
  have cfsIc1 : codomf (f_sites h) `<=` domf (smfn h').
  - apply: fsubset_trans. apply: (f_sites_in_cod h).
    by rewrite codEdom.
  set stepsA := @fcomp S S N (f_sites h) (smfn h') cfsIc1.
  have c2Idfn : codomf (smfn h) `<=` domf (f_nodes h').
  - apply: fsubset_trans. apply: fcomp_codomf.
    by apply: comp_obligation_2.
  set csmfnA := @fcomp S N N (smfn h) (f_nodes h') c2Idfn.
  have cfnIc2 : codomf (f_sites h) `<=` domf (fssm h').
  - apply: fsubset_trans. apply: (f_sites_in_cod h).
    rewrite codEdom. by apply: (eq_fsubsetLR (f_sites_total h')).
  set cfssmA := @fcomp S S N (f_sites h) (fssm h') cfnIc2.
  have -> : csmfn.[? s] = csmfnA.[? s] by apply: fcompA.
  have -> : csmfnA.[? s] = steps.[? s]
    by apply: (fcomp_eqf _ _ (comm h)).
  have <- : stepsA.[? s] = steps.[? s].
  - rewrite fcompA. apply: fsubset_trans. apply: fcomp_codomf.
    by apply: (eq_fsubsetLR (f_nodes_total h')).
    have sm2 : siteMap (dom h') = siteMap (cod h)
      by rewrite codEdom.
    have c1E : @fcomp S S N (f_sites h) (siteMap (dom h')) cfsIc1 =
                 fssm h by apply/fmapP; apply: (fcomp_eqg _ _ sm2).
    move=> c2Idfn'. by rewrite (fcomp_eqf _ _ c1E).
  have -> : stepsA.[? s] = cfssmA.[? s]
    by apply (fcomp_eqg _ _ (comm h')).
  have -> : cfssmA.[? s] = cfssm.[? s] by apply: fcompA.
  done.
Qed.
Next Obligation.
Admitted.

      ; f_nodes_total : nodes dom = domf f_nodes
      ; f_sites_total : sites dom = domf f_sites
      ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod
      ; f_sites_in_cod : codomf f_sites `<=` sites cod
      ; comm : smfn = fssm
      ; edge_pres :
        [forall s : sites dom, forall t : sites dom,
            edges dom (val s) (val t) ==
              edges cod (f_sites.[sf s]) (f_sites.[sf t])]

End Composition.
End NS.
