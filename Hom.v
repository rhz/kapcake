(* From KapCake Require Import NatMap. *)
(* Import NatMap.PartialMapNotation. *)
(* From KapCake Require Import SiteGraph. *)
(* From RecordUpdate Require Import RecordSet. *)
From mathcomp
  Require Import ssreflect ssrbool ssrnat ssrfun
  eqtype choice fintype seq finfun finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From KapCake Require Import ContactGraph.
(* Require Import Program. *)

(* Module Hom. *)
Local Open Scope fset.
Local Open Scope fmap.

(* Lemma cast (T U : Type) (H : T = U) (x : T) : U. *)
(* Proof. rewrite -H. exact x. Defined. *)
(* Definition cast (T U : Type) (H : T = U) (x : T) : U := *)
(*   eq_rect T id x U H. *)
(* Definition cast (T : choiceType) (A B : {fset T}) (H : A = B) *)
(*   (x : A) : B. *)
(* Proof. rewrite -H. exact x. Defined. *)
Definition ct (T : choiceType) (A B : {fset T}) (H : A = B)
  (x : A) : B := eq_rect A id x B H.
Definition ctt (T : choiceType) (A B : {fset T}) (H : B = A)
  (x : A) : B := eq_rect A id x B (Logic.eq_sym H).
(* Unset Printing Notations. *)
(* Print ct. *)

Search _ (_ `<=` _) (_ = _). Search "eqEfsubset".
Lemma eqEfsubset_id (T : choiceType) (A B : {fset T}) :
  A = B -> A `<=` B.
Proof. move/eqP. by rewrite eqEfsubset => /andP[H _]. Qed.
Lemma eqEfsubset_opp (T : choiceType) (A B : {fset T}) :
  A = B -> B `<=` A.
Proof. move/eqP. by rewrite eqEfsubset => /andP[_ H]. Qed.

(* Section FinMap. *)
(* Variables (K V : choiceType). *)
(* Variable (f : {fmap K -> V}). *)
(* Definition is_total (A : {fset K}) (B : {fset V}) := *)
(*   [forall a : A, exists b : B, *)
(*       f.[? (val a)] == Some (val b)] *)
(* End FinMap. *)

Section NS.
(* Types for nodes and sites *)
Variables (N S : choiceType).
(* Variables (K V1 V2 : choiceType). *)
(* Variables (f : {fmap K -> V1}) (g : {fmap K -> V2}). *)
(* Hypothesis (H : domf f = domf g). *)
(* Variable (x : domf f). *)
(* Check (g x). *)

(***** Homomorphisms *****)

(* A homomorphism h : G -> G' of
   site graphs is a pair of total functions,
   h_S : S_G -> S_G' and h_A : A_G -> A_G',
   such that for all s,s' ∈ S_G we have
   (i) h_A(σ_G(s)) = σ_G'(h_S(s)) and
   (ii) if s E_G s0 then h_S(s) E_G' h_S(s').
 *)
(* Variables (f_nodes : {fmap N -> N}) *)
(*           (f_sites : {fmap S -> S}) *)
(*           (dom : cg N S) *)
(*           (cod : cg N S). *)
(* Hypotheses (f_nodes_total : nodes dom = domf f_nodes) *)
(*            (f_sites_total : sites dom = domf f_sites). *)
(* Hypotheses (f_nodes_sub_cod : codomf f_nodes `<=` nodes cod) *)
(*            (f_sites_sub_cod : codomf f_sites `<=` sites cod). *)
(* Definition a : domf f_nodes = nodes dom. *)
(* Proof. symmetry in f_nodes_total. exact f_nodes_total. Defined. *)
(* Print a. *)
(* Definition node_in_cod_of_site (s : sites dom) : N. *)
(* Proof. refine (f_nodes.[_]). rewrite -f_nodes_total. *)
(*        exact: (in_codomf s). *)
(* Defined. *)
(* Print node_in_cod_of_site. *)
(* Coercion nodes_dom_is_domf_f_nodes (n : nodes dom) : domf f_nodes. *)
(* Proof. rewrite -f_nodes_total. exact: n. Defined. *)
(* Print nodes_dom_is_domf_f_nodes. *)
(* Section T1. *)
(* Variable (s : sites dom). *)
(* Check (in_codomf s). *)
(* About in_codomf. *)
(* Check f_nodes.[in_codomf s]. *)
(* Check in_codomf (s : domf f_sites). *)
(* Check (siteMap cod).[in_codomf (s : domf f_sites)]. *)
(* About fsubsetP. *)
(* Check (fsubsetP f_sites_sub_cod). *)
(* Lemma a : True. *)
(* Proof. move: f_sites_sub_cod => /fsubsetP H. rewrite /sub_mem in H. *)
(*        pose fs' := (in_codomf (s : domf f_sites)). *)
(*        pose s' := fs' f_sites_total. *)
(*        Search _ (_ \in _). *)
(*        move: (H (val [`s']) s') => H1. *)
(* Admitted. *)
(* Definition s' := in_codomf (ct f_sites_total s). *)
(* End T1. *)
(* Coercion sites_dom_is_domf_f_sites (s : sites dom) : domf f_sites. *)
(* Proof. rewrite -f_sites_total. exact: s. Defined. *)

(* Record same_dom (K V1 V2 : choiceType) *)
(*   (f1 : {fmap K -> V1}) (f2 : {fmap K -> V2}) : Type := *)
(*   SameDom { sameDom : domf f1 = domf f2 }. *)
(* Record chainable (K V1 V2 : choiceType) *)
(*   (f : {fmap K -> V1}) (g : {fmap V1 -> V2}) : Type := *)
(*   Chainable { codInDom : codomf f `<=` domf g }. *)
(* Record same_cod (K1 K2 V : choiceType) *)
(*   (f1 : {fmap K1 -> V}) (f2 : {fmap K2 -> V}) : Type := *)
(*   SameCod { sameCod : codomf f1 = codomf f2 }. *)
(* Record cod_is_dom (K V1 V2 : choiceType) *)
(*   (f : {fmap K -> V1}) (g : {fmap V1 -> V2}) : Type := *)
(*   CodIsDom { codIsDom : codomf f = domf g }. *)

Definition change_dom (K V1 V2 : choiceType)
  (f1 : {fmap K -> V1}) (f2 : {fmap K -> V2})
  (same_dom : domf f1 == domf f2) (x : domf f1) : domf f2 :=
  eq_rect (domf f1) id x (domf f2) (eqP same_dom).

Definition fapply (K V1 V2 : choiceType)
  (f : {fmap K -> V1}) (g : {fmap V1 -> V2})
  (chainable : codomf f `<=` domf g) (x : domf f) : _ \in codomf g :=
  let xTf : _ \in codomf f := in_codomf x in
  let xIg : _ \in domf g := (fsubsetP chainable) (val [`xTf]) xTf
  in in_codomf [`xIg].

(* Definition eq_fsubset_id' (T : choiceType) (A B : {fset T}) : *)
(*   A == B -> (A `<=` B) := *)
(*   eq_ind_r (fun x : bool => x -> A `<=` B) *)
(*     (* (fun x => match elimTF andP x with conj a b => a end) *) *)
(*     (fun x => (elimTF andP x).1) *)
(*     (eqEfsubset A B). *)
Lemma eq_fsubset_id (T : choiceType) (A B : {fset T}) :
  A == B -> A `<=` B.
Proof. by rewrite eqEfsubset => /andP[H _]. Qed.

(* Coercion eq_fsubset (T : choiceType) (A B : {fset T}) *)
(*   (H : A == B) : A `<=` B := eq_fsubset_id H. *)

(* Variables (f_nodes : {fmap N -> N}) *)
(*           (f_sites : {fmap S -> S}) *)
(*           (dom : cg N S) *)
(*           (cod : cg N S). *)
(* Hypotheses (f_nodes_total : nodes dom == domf f_nodes) *)
(*            (f_sites_total : sites dom == domf f_sites). *)
(* Hypotheses (f_nodes_in_cod : codomf f_nodes `<=` nodes cod) *)
(*            (f_sites_in_cod : codomf f_sites `<=` sites cod). *)

(* Variable (s : sites dom). *)
(* Check fapply (eq_fsubset_id f_nodes_total) s : _ \in codomf f_nodes. *)
(* Check fapply f_sites_in_cod *)
(*   (@change_dom _ N S (siteMap dom) f_sites f_sites_total s) *)
(*   : _ \in nodes cod. *)
(* Check [`fapply (eq_fsubset_id f_nodes_total) s] : codomf f_nodes. *)
(* Check [`fapply f_sites_in_cod *)
(*          (@change_dom _ N S (siteMap dom) f_sites *)
(*             f_sites_total s)] : nodes cod. *)
(* Check (fsubsetP f_nodes_in_cod) : forall x : _, *)
(*     x \in codomf f_nodes -> x \in nodes cod. *)
(* Check (fsubsetP f_nodes_in_cod) _ *)
(*   (fapply (eq_fsubset_id f_nodes_total) s) : _ \in nodes cod. *)
(* Check [`(fsubsetP f_nodes_in_cod) _ *)
(*   (fapply (eq_fsubset_id f_nodes_total) s)] == *)
(*         [`fapply f_sites_in_cod *)
(*            (@change_dom _ N S (siteMap dom) f_sites *)
(*               f_sites_total s)]. *)

(* Record hom : Type := *)
(*   Hom { dom : cg N S *)
(*       ; cod : cg N S *)
(*       ; f_nodes : {fmap N -> N} *)
(*       ; f_sites : {fmap S -> S} *)
(*     }. *)

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
      (* ; comm : [forall s : sites dom, *)
      (*       let s' : _ \in codomf f_sites := *)
      (*         in_codomf (ct f_sites_total s) in *)
      (*       let s'_in_sites_cod : _ \in sites cod := *)
      (*         (fsubsetP f_sites_sub_cod) (val [`s']) s' in *)
      (*       let n : _ \in nodes dom := in_codomf s in *)
      (*       let H : nodes dom `<=` domf f_nodes := *)
      (*         eqEfsubset_id f_nodes_total in *)
      (*       let n' : _ \in domf f_nodes := (fsubsetP H) (val [`n]) n in *)
      (*       f_nodes.[n'] == (siteMap cod).[s'_in_sites_cod]] *)
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

(*
Module HomMixin.
Section HomMixin.
  Context (N S : choiceType)
          (dom : cg N S)
          (cod : cg N S)
          (f_nodes : {fmap N -> N})
          (f_sites : {fmap S -> S})
          (f_nodes_total : nodes dom = domf f_nodes)
          (f_sites_total : sites dom = domf f_sites)
          (f_nodes_sub_cod : codomf f_nodes `<=` nodes cod)
          (f_sites_sub_cod : codomf f_sites `<=` sites cod).
  Local Coercion ndom_to_fdom (n : nodes dom) : domf f_nodes :=
    eq_rect (nodes dom) id n (domf f_nodes) f_nodes_total.
  Local Coercion sdom_to_fdom (s : sites dom) : domf f_sites :=
    eq_rect (sites dom) id s (domf f_sites) f_sites_total.
  Local Coercion fcod_to_ncod (n : codomf f_fnodes) : nodes cod :=
    (fsubsetP f_nodes_sub_cod) [`n]

  Record HomMixin := {
    comm : [forall s : sites dom,
            f_nodes (siteMap dom s) == siteMap cod (f_sites s)]
    (* and also edge_pres *)
    (* here we can rely on local coercions like `foo` when defining ` *)
  }.
End HomMixin.
End HomMixin.

Record Hom := {
  dom : ...; f_nodes : ...; f_nodes_total : ...;
  hom_mixin : HomMixin dom f_nodes f_nodes_total
}.
(* Now we can define _global_ coercions indexed by `Hom`, if we want: *)
Global Coercion foo_global (h : Hom) : nodes (dom h) >-> domf (f_nodes h) := eq_rect ... f_nodes_total.

(* Boilerplate: lift properties *)
Lemma comm (h : Hom) : [forall s : sites (dom h),
            f_nodes h (siteMap h dom s) == siteMap h cod (f_sites h s).
Proof. (* compose hom_mixin and HomMixin.comm, sth like *) apply: HomMixin.comm. exact: hom_mixin. Qed.
 *)
