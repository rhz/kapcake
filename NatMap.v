From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.

Module NatMap.

(***** Total maps *****)

Definition total (A : Type) := nat -> A.
Definition t_empty {A : Type} (v : A) : total A := (fun _ => v).
Definition t_update {A : Type} (m : total A) (x : nat) (v : A) :=
  fun x' => if x =? x' then v else m x'.

Module TotalMapNotation.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).
End TotalMapNotation.
Import TotalMapNotation.

Lemma t_apply_empty : forall (A : Type) (x : nat) (v : A),
    (_ !-> v) x = v.
Proof. intros. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total A) x v,
    (x !-> v ; m) x = v.
Proof. intros. unfold t_update. rewrite Nat.eqb_refl.
       reflexivity. Qed.

Theorem t_update_neq : forall (A : Type) (m : total A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof. intros. unfold t_update. apply Nat.eqb_neq in H.
       rewrite H. reflexivity. Qed.

Lemma t_update_shadow : forall (A : Type) (m : total A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros x'. destruct (Nat.eqb_spec x x').
  + reflexivity.
  + reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros y. destruct (Nat.eqb_spec x y) as [eq_xy | neq_xy].
  + rewrite eq_xy. reflexivity.
  + reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total A) v1 v2 x1 x2,
  x2 <> x1 -> (x1 !-> v1 ; x2 !-> v2 ; m) =
              (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros y. destruct (Nat.eqb_spec x1 y) as [eq_x1y | neq_x1y],
      (Nat.eqb_spec x2 y) as [eq_x2y | neq_x2y].
  - exfalso. apply H. apply (eq_trans_r eq_x2y eq_x1y).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(***** Partial maps *****)

Definition partial (A : Type) := total (option A).
Definition empty {A : Type} : partial A := t_empty None.
Definition update {A : Type} (m : partial A) (x : nat) (v : A) :=
  t_update m x (Some v).

Module PartialMapNotation.
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).
End PartialMapNotation.
Import PartialMapNotation.

Lemma apply_empty : forall A x, @empty A x = None.
Proof. intros. reflexivity. Qed.

Lemma update_eq : forall (A : Type) (m : partial A) x v,
    (x |-> v ; m) x = Some v.
Proof. intros. unfold update. apply t_update_eq. Qed.

Theorem update_neq : forall (A : Type) (m : partial A) x1 x2 v,
  x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Proof. intros. unfold update. apply t_update_neq. apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof. intros. unfold update. apply t_update_shadow. Qed.

Theorem update_same : forall (A : Type) (m : partial A) x v,
  m x = Some v -> (x |-> v ; m) = m.
Proof. intros. unfold update. rewrite <- H. apply t_update_same. Qed.

Theorem update_permute : forall (A : Type) (m : partial A) x1 x2 v1 v2,
    x2 <> x1 -> (x1 |-> v1 ; x2 |-> v2 ; m) =
                (x2 |-> v2 ; x1 |-> v1 ; m).
Proof. intros. unfold update. apply t_update_permute. apply H. Qed.

Definition inclusion {A : Type} (m m' : partial A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial A) x vx,
  inclusion m m' ->
  inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold inclusion. intros A m m' x vx H. intros y vy.
  destruct (Nat.eqb_spec x y) as [eq_xy | neq_xy].
  - rewrite eq_xy. rewrite update_eq. rewrite update_eq.
    intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply neq_xy.
    + apply neq_xy.
Qed.

End NatMap.
