Require Import Program.
From KapCake Require Import finmap_ext ContactGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

Section SN.
(* Types for nodes and sites *)
Variables (S N : choiceType).

(***** Homomorphisms *****)

(* A homomorphism h : G -> G' of
   site graphs is a pair of total functions,
   h_S : S_G -> S_G' and h_A : A_G -> A_G',
   such that for all s,s' ∈ S_G we have
   (i) h_A(σ_G(s)) = σ_G'(h_S(s)) and
   (ii) if s E_G s0 then h_S(s) E_G' h_S(s').
 *)
Record hom (dom cod : cg S N) : Type :=
  Hom { f_sites : {ffun sites dom -> sites cod}
      ; f_nodes : {ffun nodes dom -> nodes cod}
      ; comm :
        [forall s : sites dom,
            f_nodes.[in_codomf s] ==
            [`in_codomf (f_sites s)]]
            (* [s ; siteMap dom ; f_nodes] == *)
            (* [s ; f_sites ; siteMap cod] *)
      ; edge_pres :
        [forall s : sites dom, forall t : sites dom,
            edges dom (val s) (val t) ==
              edges cod (val (f_sites s)) (val (f_sites t))]
    }.

(* Record hom : Type := *)
(*   Hom { dom : cg S N *)
(*       ; cod : cg S N *)
(*       ; f_sites : {fmap S -> S} *)
(*       ; f_nodes : {fmap N -> N} *)
(*       ; f_sites_total : sites dom = domf f_sites *)
(*       ; f_nodes_total : nodes dom = domf f_nodes *)
(*       ; f_sites_in_cod : codomf f_sites `<=` sites cod *)
(*       ; f_nodes_in_cod : codomf f_nodes `<=` nodes cod *)
(*       ; sf (s : sites dom) := fset_eq_inLR f_sites_total (fsvalP s) *)
(*       ; nf (n : nodes dom) := fset_eq_inLR f_nodes_total (fsvalP n) *)
(*       ; fs (s : S) (sIc : s \in codomf f_sites) := *)
(*           fsubsetP f_sites_in_cod _ sIc *)
(*       ; fn (n : N) (nIc : n \in codomf f_nodes) := *)
(*           fsubsetP f_nodes_in_cod _ nIc *)
(*       ; smfn := @fcomp S N N (siteMap dom) f_nodes *)
(*                   (eq_fsubsetLR f_nodes_total) *)
(*       ; fssm := @fcomp S S N f_sites (siteMap cod) f_sites_in_cod *)
(*       ; comm : smfn = fssm *)
(*       ; edge_pres : *)
(*         [forall s : sites dom, forall t : sites dom, *)
(*             edges dom (val s) (val t) == *)
(*               edges cod (f_sites.[sf s]) (f_sites.[sf t])] *)
(*     }. *)
(* proposal for alternative names for fields: *)
(* f_nodes = fn *)
(* f_sites = fs *)
(* f_nodes_total = fnT or fn_total *)
(* f_sites_total = fsT or fs_total *)
(* f_nodes_in_cod = fnIcod *)
(* f_sites_in_cod = fsIcod *)

(* Lemma f_sites_totalP (h : hom) (s : sites (dom h)) : *)
(*   [exists t : sites (cod h), *)
(*       (f_sites h).[? val s] == Some (val t)]. *)
(* Proof using Type. *)
(*   apply/existsP. exists [`fs (im (sf s))]. *)
(*   by rewrite Some_fnd. *)
(* Qed. *)

(* Lemma f_nodes_totalP (h : hom) (n : nodes (dom h)) : *)
(*   [exists m : nodes (cod h), *)
(*       (f_nodes h).[? val n] == Some (val m)]. *)
(* Proof using Type. *)
(*   apply/existsP. exists [`fn (im (nf n))]. *)
(*   by rewrite Some_fnd. *)
(* Qed. *)

Section Identity.
Variable (g : cg S N).

Program Definition idhom : hom g g :=
  {| f_sites := [ffun s : sites g => s]
  ;  f_nodes := [ffun n : nodes g => n]
  ;  comm := _
  ;  edge_pres := _
  |}.
Next Obligation. (* comm *)
  apply/forallP => s. by rewrite !ffunE. Qed.
Next Obligation. (* edge_pres *)
  apply/'forall_forallP => s t. by rewrite !ffunE.
Qed.

(* Program Definition idhom : hom := *)
(*   {| dom := g *)
(*   ;  cod := g *)
(*   ;  f_sites := [fmap s : sites g => val s] *)
(*   ;  f_nodes := [fmap n : nodes g => val n] *)
(*   ;  f_sites_total := erefl *)
(*   ;  f_nodes_total := erefl *)
(*   ;  f_sites_in_cod := fsubset_refl (sites g) *)
(*   ;  f_nodes_in_cod := fsubset_refl (nodes g) *)
(*   ;  comm := _ *)
(*   ;  edge_pres := _ *)
(*   |}. *)

End Identity.

Section Composition.
Variables (g1 g2 g3 : cg S N)
  (h1 : hom g1 g2) (h2 : hom g2 g3).

Program Definition comp : hom g1 g3 :=
  {| f_sites := f_sites h1 \c f_sites h2
  ;  f_nodes := f_nodes h1 \c f_nodes h2
  ;  comm := _
  ;  edge_pres := _
  |}.
Next Obligation. (* comm *)
  apply/'forall_eqP => s.
  move: (comm h1) => /'forall_eqP ch1.
  move: (comm h2) => /'forall_eqP ch2.
  have -> : (f_nodes h1 \c f_nodes h2) [`in_codomf s] =
            (f_nodes h2) [`in_codomf (f_sites h1 s)]
    by rewrite !ffunE ch1.
  have -> : (f_nodes h2) [`in_codomf (f_sites h1 s)] =
            [`in_codomf ((f_sites h1 \c f_sites h2) s)].
  - by rewrite !ffunE ch2.
  done. Qed.
Next Obligation. (* edge_pres *)
  apply/'forall_'forall_eqP => s t.
  move: (edge_pres h1) => /'forall_'forall_eqP eph1.
  move: (edge_pres h2) => /'forall_'forall_eqP eph2.
  by rewrite eph1 eph2 !ffunE.
Qed.

(* Variables (h h' : hom) *)
(*   (codEdom : cod h = dom h'). *)
(* Program Definition comp : hom := *)
(*   {| dom := dom h *)
(*   ;  cod := cod h' *)
(*   ;  f_sites := @fcomp S S S (f_sites h) (f_sites h') _ *)
(*   ;  f_nodes := @fcomp N N N (f_nodes h) (f_nodes h') _ *)
(*   ;  f_sites_total := f_sites_total h *)
(*   ;  f_nodes_total := f_nodes_total h *)
(*   ;  f_sites_in_cod := _ *)
(*   ;  f_nodes_in_cod := _ *)
(*   ;  comm := _ *)
(*   ;  edge_pres := _ *)
(*   |}. *)
(* Next Obligation. (* codomf (f_sites h) `<=` domf (f_sites h') *) *)
(*   rewrite -(f_sites_total h') -codEdom. *)
(*   by apply: (f_sites_in_cod h). Qed. *)
(* Next Obligation. (* codomf (f_nodes h) `<=` domf (f_nodes h') *) *)
(*   rewrite -(f_nodes_total h') -codEdom. *)
(*   by apply: (f_nodes_in_cod h). Qed. *)
(* Next Obligation. (* f_sites_total *) *)
(*   apply: fsubset_trans. apply: fcomp_codomf. *)
(*   apply: (f_sites_in_cod h'). Qed. *)
(* Next Obligation. (* f_nodes_total *) *)
(*   apply: fsubset_trans. apply: fcomp_codomf. *)
(*   apply: (f_nodes_in_cod h'). Qed. *)
(* Next Obligation. (* comm *) *)
(*   apply/fmapP => s. *)
(*   set cf_sites := fcomp comp_obligation_1. *)
(*   set cf_nodes := fcomp comp_obligation_2. *)
(*   set cfssm := @fcomp S S N cf_sites (siteMap (cod h')) *)
(*                  comp_obligation_3. *)
(*   set csmfn := @fcomp S N N (siteMap (dom h)) cf_nodes *)
(*                  (eq_fsubsetLR (f_nodes_total h)). *)
(*   have c1Idfn : codomf (fssm h) `<=` domf (f_nodes h'). *)
(*   - apply: fsubset_trans. apply: fcomp_codomf. *)
(*     rewrite codEdom. by apply: (eq_fsubsetLR (f_nodes_total h')). *)
(*   set steps := @fcomp S N N (fssm h) (f_nodes h') c1Idfn. *)
(*   have cfsIc1 : codomf (f_sites h) `<=` domf (smfn h'). *)
(*   - apply: fsubset_trans. apply: (f_sites_in_cod h). *)
(*     by rewrite codEdom. *)
(*   set stepsA := @fcomp S S N (f_sites h) (smfn h') cfsIc1. *)
(*   have c2Idfn : codomf (smfn h) `<=` domf (f_nodes h'). *)
(*   - apply: fsubset_trans. apply: fcomp_codomf. *)
(*     by apply: comp_obligation_2. *)
(*   set csmfnA := @fcomp S N N (smfn h) (f_nodes h') c2Idfn. *)
(*   have cfnIc2 : codomf (f_sites h) `<=` domf (fssm h'). *)
(*   - apply: fsubset_trans. apply: (f_sites_in_cod h). *)
(*     rewrite codEdom. by apply: (eq_fsubsetLR (f_sites_total h')). *)
(*   set cfssmA := @fcomp S S N (f_sites h) (fssm h') cfnIc2. *)
(*   have -> : csmfn.[? s] = csmfnA.[? s] by apply: fcompA. *)
(*   have -> : csmfnA.[? s] = steps.[? s] *)
(*     by apply: (fcomp_eqf _ _ (comm h)). *)
(*   have <- : stepsA.[? s] = steps.[? s]. *)
(*   - rewrite fcompA. apply: fsubset_trans. apply: fcomp_codomf. *)
(*     by apply: (eq_fsubsetLR (f_nodes_total h')). *)
(*     have sm2 : siteMap (dom h') = siteMap (cod h) *)
(*       by rewrite codEdom. *)
(*     have c1E : @fcomp S S N (f_sites h) (siteMap (dom h')) cfsIc1 = *)
(*                  fssm h by apply/fmapP; apply: (fcomp_eqg _ _ sm2). *)
(*     move=> c2Idfn'. by rewrite (fcomp_eqf _ _ c1E). *)
(*   have -> : stepsA.[? s] = cfssmA.[? s] *)
(*     by apply (fcomp_eqg _ _ (comm h')). *)
(*   have -> : cfssmA.[? s] = cfssm.[? s] by apply: fcompA. *)
(*   done. Qed. *)
(* Next Obligation. (* edge_pres *) *)
(*   apply/'forall_forallP => s t. apply/eqP. *)
(*   move: (edge_pres h) => /'forall_'forall_eqP eph. *)
(*   move: (edge_pres h') => /'forall_'forall_eqP eph'. *)
(*   rewrite (eph s t) codEdom. *)
(*   pose inh' xIs := fset_eq_inRL (f_sites_total h') *)
(*                      (fsubsetP comp_obligation_1 _ xIs). *)
(*   have -> : f_sites h [`sf s] = val [`inh' _ (im (sf s))] by []. *)
(*   have -> : f_sites h [`sf t] = val [`inh' _ (im (sf t))] by []. *)
(*   rewrite (eph' [`inh' _ (im (sf s))] *)
(*                 [`inh' _ (im (sf t))]) !ffunE. *)
(*   congr edges; apply: eq_getf. *)
(* Qed. *)

End Composition.

Section ContactMap.
Variables (dom cod : cg S N) (h : hom dom cod).

Definition is_contact_map : bool :=
  (* if (dom h) is realisable *)
  is_realisable dom. (* && *)
  (* node-local injectivity on sites? *)
  (* ie whenever f_sites s = f_sites t and *)
  (* siteMap (dom h) s = siteMap (dom h) t, then s = t. *)
  (* Perhaps we can get rid of this restriction. *)
  (* [forall s : sites (dom h), forall t : sites (dom h), *)
  (*     ((f_sites h).[sf s] == (f_sites h).[sf t]) && *)
  (*     (siteMap (dom h) s == siteMap (dom h) t) *)
  (*       ==> (s == t)]. *)

End ContactMap.

Section Embedding.
Variables (dom cod : cg S N) (h : hom dom cod).

(* A homomorphism ψ : G → G' is an embedding iff *)
(* (i) ψA and ψS are injective, and *)
(* (ii) if s is free in G, so is ψS(s) in G'. *)
(* Injectivity of ψA and ψS implies that *)
(* whenever ψ : G → G' is an embedding *)
(* and G' is realisable then G is also realisable. *)
Definition is_embedding : bool :=
  injectiveb (f_sites h) && injectiveb (f_nodes h) &&
  [forall s : sites dom,
      is_free dom (val s) && (val s \notin wildcards dom)
      ==> is_free cod (f_sites h s)].
(* Definition is_embedding : bool := *)
(*   injectiveb (f_sites h) && injectiveb (f_nodes h) && *)
(*   [forall s : sites (dom h), *)
(*       is_free (dom h) (val s) && (val s \notin wildcards (dom h)) *)
(*       ==> is_free (cod h) (f_sites h).[sf s]]. *)

(* Lemma emb_realisable : *)
(*   is_embedding -> is_realisable (cod h) -> is_realisable (dom h). *)
(* Proof using Type. *)
(*   move=> /andP[/andP[/injectiveP fs_inj /injectiveP fn_inj] _] *)
(*          /andP[/andP[/forallP noloop *)
(*                      /'forall_'forall_forallP atmost1e] *)
(*                /forallP wildcards_free]. *)
(*   apply/(andPP (andPP 'forall_eqP 'forall_'forall_'forall_implyP) *)
(*                'forall_implyP). split. split. *)
(*   - move=> s. Print injective. *)
(*     rewrite -(eqP (noloop [`fs (im (sf s))])). *)

End Embedding.
End NS.
