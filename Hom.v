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
      (* ; comm : [forall s : sites dom, *)
      (*       f_nodes (siteMap dom s) == siteMap cod (f_sites s) *)
      (* ; edge_pres : [forall s : sites dom, forall t : sites dom, *)
      (*       edges dom (val s) (val t) == *)
      (*         edges cod (f_sites s) (f_sites t)] *)
      ; comm :
        [forall s : sites dom, smfn s == fssm.[sf s]]
            (* f_nodes.[? siteMap dom s] == *)
            (*   (siteMap cod).[? f_sites.[sf s]]] *)
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
  apply/forallP => s.
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
  have c2Idfn : codomf (smfn h) `<=` domf (f_nodes h').
  - apply: fsubset_trans. apply: fcomp_codomf.
    by apply: comp_obligation_2.
  set csmfnA := @fcomp S N N (smfn h) (f_nodes h') c2Idfn.
  have cfnIc2 : codomf (f_sites h) `<=` domf (fssm h').
  - apply: fsubset_trans. apply: (f_sites_in_cod h).
    rewrite codEdom. by apply: (eq_fsubsetLR (f_sites_total h')).
  set cfssmA := @fcomp S S N (f_sites h) (fssm h') cfnIc2.
  (* rewrite fcompAx. apply: (eq_fsubsetLR (f_nodes_total h)). *)
  (* move=> H. Set Printing Implicit. *)
  (* apply c2Idfn. *)
  (* rewrite (fcompAx (eq_fsubsetLR (f_nodes_total h)) c2Idfn). *)
  (* have H : csmfn = csmfnA by apply fcompA. *)
  (* rewrite (fmapE _ _ H). *)
  have -> : csmfn s = csmfnA s by apply fcompAx.
  have -> : csmfnA s = steps.[sf s]. admit.
  have -> : steps.[sf s] = cfssmA.[sf s]. admit.
  have -> : cfssmA.[sf s] = cfssm.[sf s]. admit.
  done.
Admitted.

      ; f_nodes_total : nodes dom = domf f_nodes
      ; f_sites_total : sites dom = domf f_sites
      ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod
      ; f_sites_in_cod : codomf f_sites `<=` sites cod
      ; comm :
        [forall s : sites dom,
            f_nodes.[? siteMap dom s] ==
              if f_sites.[? val s] is Some s'
              then (siteMap cod).[? s'] else None]

  rewrite (@Some_fnd_eq S S this_f_sites) ?(f_sites_total h) //
          => this_f_sites_total.
  have [n Hn] : exists n : nodes (dom h),
      siteMap (dom h) s = val n.
  admit.
  rewrite Hn (@Some_fnd_eq N N this_f_nodes) ?(f_nodes_total h) //
          => this_f_nodes_total.
  apply/eqP. symmetry. apply/fndSomeP.
  set s_fs := fset_eq_inl this_f_sites_total (fsvalP s).
  have s3 : this_f_sites.[s_fs] \in siteMap (cod h').
  admit.
  exists s3.
  set n_fn := fset_eq_inl this_f_nodes_total (fsvalP n).
  have [s2 Hs2] : exists s2 : sites (dom h'),
      siteMap (cod h') [`s3] =
        (f_nodes h').[fset_eq_inl (f_nodes_total h') (in_codomf s2)].
  admit.
  rewrite Hs2.
  have Hs : s2 = [`fset_eq_inl _
                    (fsubsetP (f_sites_in_cod h) _
                       (in_codomf [`fset_eq_inl
                                     (f_sites_total h) (fsvalP s)]))].
  admit.
  rewrite Hs ?(codEdom) //= => sites_codEdom.

Admitted.
Next Obligation.
Admitted.

      ; f_nodes_total : nodes dom = domf f_nodes
      ; f_sites_total : sites dom = domf f_sites
      ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod
      ; f_sites_in_cod : codomf f_sites `<=` sites cod
      ; comm :
        [forall s : sites dom,
            f_nodes.[? siteMap dom s] ==
              if f_sites.[? val s] is Some s'
              then (siteMap cod).[? s'] else None]
      ; edge_pres :
        [forall s : sites dom, forall t : sites dom,
            edges dom (val s) (val t) ==
              if (f_sites.[? val s], f_sites.[? val t])
                   is (Some s', Some t')
              then edges cod s' t' else false]

End Composition.
End NS.
