From mathcomp Require Export eqtype fintype ssreflect ssrbool ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments val : simpl never.

Lemma forall_true (T : finType) :
  [forall x : T, true] = true.
Proof. by apply/forallP. Qed.

Lemma forall_false (T : finType) :
  [forall x : T, false] = (#|T| == 0).
Proof. done. Qed.

Lemma forall_andb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x && Q x] =
  [forall x : T, P x] && [forall x : T, Q x].
Proof. Admitted.

Lemma forall_orb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x || Q x] =
  [forall x : T, P x] || [forall x : T, Q x].
Proof. Admitted.
