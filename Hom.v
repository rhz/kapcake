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
      ; f_nodes : {fmap N -> N}
      ; f_sites : {fmap S -> S}
      ; f_nodes_total : nodes dom == domf f_nodes
      ; f_sites_total : sites dom == domf f_sites
      ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod
      ; f_sites_in_cod : codomf f_sites `<=` sites cod
      (* ; comm : [forall s : sites dom, *)
      (*       f_nodes (siteMap dom s) == siteMap cod (f_sites s) *)
      (* ; edge_pres : [forall s : sites dom, forall t : sites dom, *)
      (*       edges dom (val s) (val t) == *)
      (*         edges cod (f_sites s) (f_sites t)] *)
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
    }.

Lemma f_nodes_totalP (h : hom) (n : nodes (dom h)) :
  [exists m : nodes (cod h),
      (f_nodes h).[? val n] == Some (val m)].
Proof using Type.
  apply/existsP. move: n. rewrite (eqP (f_nodes_total h)) => n.
  exists [`fsubsetP (f_nodes_in_cod h) _ (in_codomf n)].
  by rewrite Some_fnd.
Qed.

Lemma f_sites_totalP (h : hom) (s : sites (dom h)) :
  [exists t : sites (cod h),
      (f_sites h).[? val s] == Some (val t)].
Proof using Type.
  apply/existsP. move: s. rewrite (eqP (f_sites_total h)) => s.
  exists [`fsubsetP (f_sites_in_cod h) _ (in_codomf s)].
  by rewrite Some_fnd.
Qed.

End NS.
