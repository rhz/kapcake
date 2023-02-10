From mathcomp
  Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From KapCake Require Import ContactGraph.

Local Open Scope fset.
Local Open Scope fmap.

Lemma eq_fsubset_id (T : choiceType) (A B : {fset T}) :
  A == B -> A `<=` B.
Proof. by rewrite eqEfsubset => /andP[H _]. Qed.

Definition change_dom (K V1 V2 : choiceType)
  (f1 : {fmap K -> V1}) (f2 : {fmap K -> V2})
  (same_dom : domf f1 == domf f2) (x : domf f1) : domf f2 :=
  eq_rect (domf f1) id x (domf f2) (eqP same_dom).

Definition fapply (K V1 V2 : choiceType)
  (f : {fmap K -> V1}) (g : {fmap V1 -> V2})
  (chainable : codomf f `<=` domf g) (x : domf f) : _ \in codomf g :=
  in_codomf [`(fsubsetP chainable) _ (in_codomf x)].

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
      (*       edges dom s t == *)
      (*         edges cod (f_sites s) (f_sites t)] *)
      ; comm : [forall s : sites dom,
            [`(fsubsetP f_nodes_in_cod) _
               (fapply (eq_fsubset_id f_nodes_total) s)] ==
              [`fapply f_sites_in_cod
                 (@change_dom _ N S (siteMap dom) f_sites
                    f_sites_total s)]]
      (* ; edge_pres : [forall s : sites dom, forall t : sites dom, *)
      (*       edges dom (val s) (val t) == *)
      (*         edges cod (f_sites s) (f_sites t)] *)
      (* ; f_nodes_total : *)
      (*   [forall n : nodes dom, exists m : nodes cod, *)
      (*       f_nodes.[? val n] == Some (val m)] *)
      (* ; f_sites_total : *)
      (*   [forall s : sites dom, exists t : sites cod, *)
      (*       f_sites.[? val s] == Some (val t)] *)
      (* ; comm : *)
      (*   [forall s : sites dom, *)
      (*       f_nodes.[? siteMap dom s] == *)
      (*         obind (fun s' => (siteMap cod).[? s']) *)
      (*           f_sites.[? val s]] *)
      (* ; edge_pres : *)
      (*   [forall s : sites dom, forall t : sites dom, *)
      (*       edges dom (val s) (val t) == *)
      (*         if (f_sites.[? val s], f_sites.[? val t]) *)
      (*              is (Some s', Some t') *)
      (*         then edges cod s' t' else false] *)
    }.

End NS.
