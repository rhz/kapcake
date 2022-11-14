From KapCake Require Import NatMap.
Import NatMap.PartialMapNotation.
From KapCake Require Import SiteGraph.
From RecordUpdate Require Import RecordSet.

(***** Homomorphisms *****)

(* A homomorphism h : G -> G' of
   site graphs is a pair of total functions,
   h_S : S_G -> S_G' and h_A : A_G -> A_G',
   such that for all s,s' ∈ S_G we have
   (i) h_A(σ_G(s)) = σ_G'(h_S(s)) and
   (ii) if s E_G s0 then h_S(s) E_G' h_S(s').
 *)
Record Hom : Type :=
  mkHom
    { f_nodes : NatMap.partial nat
    ; f_sites : NatMap.partial nat
    }.
#[export] Instance etaHom : Settable _ :=
  settable! mkHom <f_nodes; f_sites>.
