From mathcomp
Require Export eqtype fintype ssrbool ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma forall_true (T : finType) :
  [forall x : T, true] = true.
Proof. by apply/forallP. Qed.

Lemma forall_false (T : finType) :
  [forall x : T, false] = false.
Proof. have x : T by admit.
       by apply/forallP => /(_ x) H.
Admitted.

Lemma forall_andb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x && Q x] =
  [forall x : T, P x] && [forall x : T, Q x].
Proof. Admitted.

Lemma forall_orb (T : finType) (P Q : T -> bool) :
  [forall x : T, P x || Q x] =
  [forall x : T, P x] || [forall x : T, Q x].
Proof. Admitted.
