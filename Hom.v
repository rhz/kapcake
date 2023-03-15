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
      ; comm : [siteMap dom ; f_nodes] =
               [f_sites ; siteMap cod]
      ; edge_pres :
        [forall s : sites dom, forall t : sites dom,
            edges dom s t ==
              edges cod (f_sites s) (f_sites t)]
    }.

Section Identity.
Variable (g : cg S N).

Program Definition idhom : hom g g :=
  {| f_sites := [ffun s : sites g => s]
  ;  f_nodes := [ffun n : nodes g => n]
  ;  comm := _
  ;  edge_pres := _
  |}.
Next Obligation. (* comm *)
  apply/ffunP => s. by rewrite !ffunE. Qed.
Next Obligation. (* edge_pres *)
  apply/'forall_forallP => s t. by rewrite !ffunE.
Qed.

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
  move: (comm h1) (comm h2) => /= ch1 ch2.
  by rewrite ffcompA -ch2 -ffcompA ch1 ffcompA. Qed.
Next Obligation. (* edge_pres *)
  apply/'forall_'forall_eqP => s t.
  move: (edge_pres h1) => /'forall_'forall_eqP eph1.
  move: (edge_pres h2) => /'forall_'forall_eqP eph2.
  by rewrite eph1 eph2 !ffunE.
Qed.

End Composition.

Section ContactMap.
(* Definition is_contact_map (dom cod : cg S N) (h : hom dom cod) *)
(*   : bool := is_realisable dom. *)
Variable (contact_graph : cg S N).

Record cm :=
  CM { graph :> cg S N
     ; dom_is_realisable : is_realisable graph
     ; cmap :> hom graph contact_graph
    }.

End ContactMap.

Section Embedding.
Section IsEmb.
Variables (dom cod : cg S N) (h : hom dom cod).

(* A homomorphism ψ : G → G' is an embedding iff *)
(* (i) ψA and ψS are injective, and *)
(* (ii) if s is free in G, so is ψS(s) in G'. *)
(* Injectivity of ψA and ψS implies that *)
(* whenever ψ : G → G' is an embedding *)
(* and G' is realisable then G is also realisable. *)
Definition is_embedding : bool :=
  [&& injectiveb (f_sites h),
      injectiveb (f_nodes h)
    & [forall s : sites dom,
        is_free dom s && (val s \notin wildcards dom) ==>
        is_free cod (f_sites h s)]].

Definition IsEmbedding : Prop :=
  [/\ injective (f_sites h),
      injective (f_nodes h)
    & forall s : sites dom,
        is_free dom s && (val s \notin wildcards dom) ->
        is_free cod (f_sites h s)].

Lemma embP : reflect IsEmbedding is_embedding.
Proof using Type.
  exact: (and3PP (injectiveP _) (injectiveP _) 'forall_implyP).
Qed.

(* Realisability backpropagates through embeddings. *)
Lemma emb_realisable :
  is_embedding -> is_realisable cod -> is_realisable dom.
Proof using Type.
  move=> /embP [fs_inj fn_inj free_pres]
         /realP [noloop atmost1e].
  move: (edge_pres h) => /'forall_'forall_eqP eph.
  apply/realP. split.
  - move=> s. rewrite eph. apply: (noloop (f_sites h s)).
  - move=> s t t'. rewrite !eph => /(atmost1e _ _ _) ftEft'.
    by apply: fs_inj.
Qed.
End IsEmb.

(* lifted embedding *)
Record emb (contact_graph : cg S N)
  (source target : cm contact_graph) :=
  Emb { ehom :> hom (graph source) (graph target)
      ; hom_is_emb : is_embedding ehom
      ; fs_comm : [f_sites ehom ; f_sites target] =
                  f_sites source
      ; fn_comm : [f_nodes ehom ; f_nodes target] =
                  f_nodes source
    }.

End Embedding.
End SN.
