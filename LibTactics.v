(* Tactics taken and derived from
   https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html

   Original author: Arthur Chargueraud
 *)
Set Implicit Arguments.
Require Coq.ZArith.BinInt.

Declare Scope ltac_scope.

(** [show tac] executes a tactic [tac] that produces a result,
    and then display its result. *)
Tactic Notation "show" tactic(tac) :=
  let R := tac in pose R.

(* ================================================================= *)
(** ** Wildcard Arguments for Tactics  *)

(** [ltac_wild] is a constant that can be used to simulate
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set :=
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set :=
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.

(* ================================================================= *)
(** ** Position Markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(* ================================================================= *)
(** ** Deconstructing Terms *)

(** [get_head E] is a tactic that returns the head constant of the
    term [E], ie, when applied to a term of the form [P x1 ... xN]
    it returns [P]. If [E] is not an application, it returns [E].
    Warning: the tactic seems to loop in some cases when the goal is
    a product and one uses the result of this function. *)

Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

(* ================================================================= *)
(** ** Numbers as Arguments *)

(** When tactic takes a natural number as argument, it may be
    parsed either as a natural number or as a relative number.
    In order for tactics to convert their arguments into natural numbers,
    we provide a conversion tactic.

    Note: the tactic [number_to_nat] is extended in [LibInt] to
    take into account the [Z] type. *)

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.

(* ================================================================= *)
(** ** Absurd Goals *)

(** [false_goal] replaces any goal by the goal [False].
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  elimtype False.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *)

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(** [false_invert H] proves a goal if it absurd after
    calling [inversion H] and [false] *)

Ltac false_invert_for H :=
  let M := fresh "TEMP" in pose (M := H); inversion H; false.

Tactic Notation "false_invert" constr(H) :=
  try solve [ false_invert_for H | false ].

(** [false_invert] proves any goal provided there is at least
    one hypothesis [H] in the context (or as a universally quantified
    hypothesis visible at the head of the goal) that can be proved absurd by calling
    [inversion H]. *)

Ltac false_invert_iter :=
  match goal with H:_ |- _ =>
    solve [ inversion H; false
          | clear H; false_invert_iter
          | fail 2 ] end.

Tactic Notation "false_invert" :=
  intros; solve [ false_invert_iter | false ].

(** [tryfalse_invert H] and [tryfalse_invert] are like the
    above but leave the goal unchanged if they don't solve it. *)

Tactic Notation "tryfalse_invert" constr(H) :=
  try (false_invert H).

Tactic Notation "tryfalse_invert" :=
  try false_invert.

(* ================================================================= *)
(** ** Introduction *)

(** [introv] is used to name only non-dependent hypothesis.
 - If [introv] is called on a goal of the form [forall x, H],
   it should introduce all the variables quantified with a
   [forall] at the head of the goal, but it does not introduce
   hypotheses that preceed an arrow constructor, like in [P -> Q].
 - If [introv] is called on a goal that is not of the form
   [forall x, H] nor [P -> Q], the tactic unfolds definitions
   until the goal takes the form [forall x, H] or [P -> Q].
   If unfolding definitions does not produces a goal of this form,
   then the tactic [introv] does nothing at all. *)

(* [introv_rec] introduces all visible variables.
   It does not try to unfold any definition. *)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.

(* [introv_noarg] forces the goal to be a [forall] or an [->],
   and then calls [introv_rec] to introduce variables
   (possibly none, in which case [introv] is the same as [hnf]).
   If the goal is not a product, then it does not do anything. *)

Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

(* [introv_arg H] introduces one non-dependent hypothesis
   under the name [H], after introducing the variables
   quantified with a [forall] that preceeds this hypothesis.
   This tactic fails if there does not exist a hypothesis
   to be introduced. *)
(* Note: __ in introv means "intros" *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* ================================================================= *)
(** ** Generalization *)

(** [gen X1 .. XN] is a shorthand for calling [generalize dependent]
    successively on variables [XN]...[X1]. Note that the variables
    are generalized in reverse order, following the convention of
    the [generalize] tactic: it means that [X1] will be the first
    quantified variable in the resulting goal. *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) :=
  gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) :=
  gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) :=
  gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) :=
  gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
  gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.

(* ================================================================= *)
(** ** Renaming *)

(** [renames X1 to Y1, ..., XN to YN] is a shorthand for a sequence of
    renaming operations [rename Xi into Yi]. *)

Tactic Notation "renames" ident(X1) "to" ident(Y1) :=
  rename X1 into Y1.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) :=
  renames X1 to Y1; renames X2 to Y2.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) ","
 ident(X6) "to" ident(Y6) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5, X6 to Y6.

(* ================================================================= *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first.
    -- warning: this tactic is overriden in LibReflect. *)

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

(** [unfolds in H] unfolds the head definition of hypothesis [H], i.e. if
    [H] has type [P x1 ... xN] then it calls [unfold P in H]. *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.

(** [unfolds in H1,H2,..,HN] allows unfolding the head constant
    in several hypotheses at once. *)

Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
  unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
  unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
  unfolds in H1; unfolds in H2 H3 H4 H5.

(** [unfolds P1,..,PN] is a shortcut for [unfold P1,..,PN in *]. *)

Tactic Notation "unfolds" constr(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2) :=
  unfold F1,F2 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) :=
  unfold F1,F2,F3 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) :=
  unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) "," constr(F6) :=
  unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) :=
  unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) "," constr(F8) :=
  unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.

(** [folds P1,..,PN] is a shortcut for [fold P1 in *; ..; fold PN in *]. *)

Tactic Notation "folds" constr(H) :=
  fold H in *.
Tactic Notation "folds" constr(H1) "," constr(H2) :=
  folds H1; folds H2.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3) :=
  folds H1; folds H2; folds H3.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) :=
  folds H1; folds H2; folds H3; folds H4.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) "," constr(H5) :=
  folds H1; folds H2; folds H3; folds H4; folds H5.

(* ================================================================= *)
(** ** Simplification *)

(** [simpls] is a shortcut for [simpl in *]. *)

Tactic Notation "simpls" :=
  simpl in *.

(** [simpls P1,..,PN] is a shortcut for
    [simpl P1 in *; ..; simpl PN in *]. *)

Tactic Notation "simpls" constr(F1) :=
  simpl F1 in *.
Tactic Notation "simpls" constr(F1) "," constr(F2) :=
  simpls F1; simpls F2.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) :=
  simpls F1; simpls F2; simpls F3.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  simpls F1; simpls F2; simpls F3; simpls F4.

(* ================================================================= *)
(** ** Substitution *)

(** [substs] does the same as [subst], except that it does not fail
    when there are circular equalities in the context. *)

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

(* ================================================================= *)
(** ** Proving Equalities *)

(** The tactic [fequal] enhances Coq's tactic [f_equal], which does not
    simplify equalities between tuples, nor between dependent pairs of
    the form [exist _ _] or [existT _ _]. For support of dependent pairs,
    the file [LibEqual] must be imported.

    Subgoals solvable by [reflexivity] are automatically discharged.
    See also the the variant [fequals], which discharges more subgoals. *)

(** Note: only [args_eq_2] is actually useful for the implementation of
    [fequal], if we rely on Coq's [f_equal] tactic for other arities.
    We provide these lemmas to show the pattern of lemmas to exploit
    for implementing [fequal] independently of [f_equal]. *)

Section FuncEq.
Variables (A1 A2 A3 A4 A5 A6 A7 B : Type).

Lemma args_eq_1 : forall (f:A1->B) x1 y1,
  x1 = y1 ->
  f x1 = f y1.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_2 : forall (f:A1->A2->B) x1 y1 x2 y2,
  x1 = y1 -> x2 = y2 ->
  f x1 x2 = f y1 y2.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_3 : forall (f:A1->A2->A3->B) x1 y1 x2 y2 x3 y3,
  x1 = y1 -> x2 = y2 -> x3 = y3 ->
  f x1 x2 x3 = f y1 y2 y3.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_4 : forall (f:A1->A2->A3->A4->B) x1 y1 x2 y2 x3 y3 x4 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 ->
  f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_5 : forall (f:A1->A2->A3->A4->A5->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 ->
  f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_6 : forall (f:A1->A2->A3->A4->A5->A6->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 ->
  f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_7 : forall (f:A1->A2->A3->A4->A5->A6->A7->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 ->
  f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7.
Proof using. intros. subst. auto. Qed.

End FuncEq.

Ltac fequal_post :=
  try solve [ reflexivity ].

(** [fequal_support_for_exist], implemented in [LibEqual], is meant
   to simplify goals of the form [exist _ _ = exist _ _ ] and
   [existT _ _ = existT _ _], by exploiting proof irrelevance. *)

Ltac fequal_support_for_exist tt :=
  fail.

(** For a n-ary tuple, [fequal], unlike [f_equal] enforces a recursive call
    on the (n-1)-ary tuple associated with the right component. *)

Ltac fequal_base :=
  match goal with
  | |- (_,_,_) = (_,_,_) =>  apply args_eq_2; [ fequal_base | ]
  | |- _ => first
            [ fequal_support_for_exist tt
            | apply args_eq_1
            | apply args_eq_2
            | apply args_eq_3
            | apply args_eq_4
            | apply args_eq_5
            | apply args_eq_6
            | apply args_eq_7
            | f_equal (* fallback to Coq [f_equal] *) ]
  end.

Tactic Notation "fequal" :=
  fequal_base; fequal_post.

(* ================================================================= *)
(** ** Injection with Substitution *)

(** Underlying implementation of [injects] *)

Ltac injects_tactic H :=
  let rec go _ :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y | idtac ];
                           go tt
    end in
  generalize ltac_mark; injection H; go tt.

(** [injects keep H] takes an hypothesis [H] of the form
    [C a1 .. aN = C b1 .. bN] and substitute all equalities
    [ai = bi] that have been generated. *)

Tactic Notation "injects" "keep" hyp(H) :=
  injects_tactic H.

(** [injects H] is similar to [injects keep H] but clears
    the hypothesis [H]. *)

Tactic Notation "injects" hyp(H) :=
  injects_tactic H; clear H.

(** [inject H as X1 .. XN] is the same as [injection]
    followed by [intros X1 .. XN] *)

Tactic Notation "inject" hyp(H) :=
  injection H.
Tactic Notation "inject" hyp(H) "as" ident(X1) :=
  injection H; intros X1.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) :=
  injection H; intros X1 X2.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3) :=
  injection H; intros X1 X2 X3.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) :=
  injection H; intros X1 X2 X3 X4.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) ident(X5) :=
  injection H; intros X1 X2 X3 X4 X5.

(* ================================================================= *)
(** ** Case Analysis *)

(** [def_to_eq E X H] applies when [X := E] is a local
    definition. It adds an assumption [H: X = E]
    and then clears the definition of [X].
    [def_to_eq_sym] is similar except that it generates
    the equality [H: E = X]. *)

Ltac def_to_eq X HX E :=
  assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

(** [cases] is similar to [case_eq E] except that it generates the
    equality in the context and not in the goal, and generates the
    equality the other way round. The syntax [cases E as H]
    allows specifying the name [H] of that hypothesis. *)

Tactic Notation "cases" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq_sym X H E;
  destruct X.

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.

(* ################################################################# *)
(** * Decidable Equality *)

(** [decides_equality] is the same as [decide equality] excepts that it
    is able to unfold definitions at head of the current goal. *)

Ltac decides_equality_tactic :=
  first [ decide equality | progress(unfolds); decides_equality_tactic ].

Tactic Notation "decides_equality" :=
  decides_equality_tactic.

(* ################################################################# *)
(** * Equivalence *)

(** [iff H] can be used to prove an equivalence [P <-> Q] and name [H]
    the hypothesis obtained in each case. The syntaxes [iff] and [iff H1 H2]
    are also available to specify zero or two names. The tactic [iff <- H]
    swaps the two subgoals, i.e. produces (Q -> P) as first subgoal. *)

Lemma iff_intro_swap : forall (P Q : Prop),
  (Q -> P) -> (P -> Q) -> (P <-> Q).
Proof using. intuition. Qed.

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
  split; [ intros H1 | intros H2 ].
Tactic Notation "iff" simple_intropattern(H) :=
  iff H H.
Tactic Notation "iff" :=
  let H := fresh "H" in iff H.

Tactic Notation "iff" "<-" simple_intropattern(H1) simple_intropattern(H2) :=
  apply iff_intro_swap; [ intros H1 | intros H2 ].
Tactic Notation "iff" "<-" simple_intropattern(H) :=
  iff <- H H.
Tactic Notation "iff" "<-" :=
  let H := fresh "H" in iff <- H.

(* ################################################################# *)
(** * N-ary Conjunctions and Disjunctions *)

(** N-ary Conjunctions Splitting in Goals *)

(** Underlying implementation of [splits]. *)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

Ltac unfold_goal_until_conjunction :=
  match goal with
  | |- _ /\ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_conjunction
  end.

Ltac get_term_conjunction_arity T :=
  match T with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
  | _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
  | _ /\ _ /\ _ /\ _ => constr:(4)
  | _ /\ _ /\ _ => constr:(3)
  | _ /\ _ => constr:(2)
  | _ -> ?T' => get_term_conjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_conjunction_arity T'
         end
         (* --todo: warning this can loop... *)
  end.

Ltac get_goal_conjunction_arity :=
  match goal with |- ?T => get_term_conjunction_arity T end.

(** [splits] applies to a goal of the form [(T1 /\ .. /\ TN)] and
    destruct it into [N] subgoals [T1] .. [TN]. If the goal is not a
    conjunction, then it unfolds the head definition. *)

Tactic Notation "splits" :=
  unfold_goal_until_conjunction;
  let N := get_goal_conjunction_arity in
  splits_tactic N.

(** [splits N] is similar to [splits], except that it will unfold as many
    definitions as necessary to obtain an [N]-ary conjunction. *)

Tactic Notation "splits" constr(N) :=
  let N := number_to_nat N in
  splits_tactic N.

(** N-ary Conjunctions Deconstruction *)

(** Underlying implementation of [destructs]. *)

Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
  | 4 => destruct T as [? [? [? ?]]]
  | 5 => destruct T as [? [? [? [? ?]]]]
  | 6 => destruct T as [? [? [? [? [? ?]]]]]
  | 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
  end.

(** [destructs T] allows destructing a term [T] which is a N-ary
    conjunction. It is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. *)

Tactic Notation "destructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  destructs_conjunction_tactic N T.

(** [destructs N T] is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. Remark that it is not restricted to N-ary conjunctions. *)

Tactic Notation "destructs" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_conjunction_tactic N T.

(** Proving Goals that are N-ary Disjunctions *)

(** Underlying implementation of [branch]. *)

Ltac branch_tactic K N :=
  match constr:((K,N)) with
  | (_,0) => fail 1
  | (0,_) => fail 1
  | (1,1) => idtac
  | (1,_) => left
  | (S ?K', S ?N') => right; branch_tactic K' N'
  end.

Ltac unfold_goal_until_disjunction :=
  match goal with
  | |- _ \/ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_disjunction
  end.

Ltac get_term_disjunction_arity T :=
  match T with
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(8)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(7)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(6)
  | _ \/ _ \/ _ \/ _ \/ _ => constr:(5)
  | _ \/ _ \/ _ \/ _ => constr:(4)
  | _ \/ _ \/ _ => constr:(3)
  | _ \/ _ => constr:(2)
  | _ -> ?T' => get_term_disjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_disjunction_arity T'
         end
  end.

Ltac get_goal_disjunction_arity :=
  match goal with |- ?T => get_term_disjunction_arity T end.

(** [branch N] applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK].
    It only able to unfold the head definition (if there is one),
    but for more complex unfolding one should use the tactic
    [branch K of N]. *)

Tactic Notation "branch" constr(K) :=
  let K := number_to_nat K in
  unfold_goal_until_disjunction;
  let N := get_goal_disjunction_arity in
  branch_tactic K N.

(** [branch K of N] is similar to [branch K] except that the
    arity of the disjunction [N] is given manually, and so this
    version of the tactic is able to unfold definitions.
    In other words, applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK]. *)

Tactic Notation "branch" constr(K) "of" constr(N) :=
  let N := number_to_nat N in
  let K := number_to_nat K in
  branch_tactic K N.

(** N-ary Disjunction Deconstruction *)

(** Underlying implementation of [branches]. *)

Ltac destructs_disjunction_tactic N T :=
  match N with
  | 2 => destruct T as [T | T]
  | 3 => destruct T as [T | [T | T]]
  | 4 => destruct T as [T | [T | [T | T]]]
  | 5 => destruct T as [T | [T | [T | [T | T]]]]
  end.

(** [branches T] allows destructing a term [T] which is a N-ary
    disjunction. It is equivalent to [destruct T as [ H1 | .. | HN ] ],
    and produces [N] subgoals corresponding to the [N] possible cases. *)

Tactic Notation "branches" constr(T) :=
  let TT := type of T in
  let N := get_term_disjunction_arity TT in
  destructs_disjunction_tactic N T.

(** [branches N T] is the same as [branches T] except that the arity is
    forced to [N]. This version is useful to unfold definitions
    on the fly. *)

Tactic Notation "branches" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_disjunction_tactic N T.

(** [branches] automatically finds a hypothesis [h] that is a disjunction
    and destructs it. *)

Tactic Notation "branches" :=
  match goal with h: _ \/ _ |- _ => branches h end.

(** N-ary Existentials *)

(* Underlying implementation of [exists]. *)

Ltac get_term_existential_arity T :=
  match T with
  | exists x1 x2 x3 x4 x5 x6 x7 x8, _ => constr:(8)
  | exists x1 x2 x3 x4 x5 x6 x7, _ => constr:(7)
  | exists x1 x2 x3 x4 x5 x6, _ => constr:(6)
  | exists x1 x2 x3 x4 x5, _ => constr:(5)
  | exists x1 x2 x3 x4, _ => constr:(4)
  | exists x1 x2 x3, _ => constr:(3)
  | exists x1 x2, _ => constr:(2)
  | exists x1, _ => constr:(1)
  | _ -> ?T' => get_term_existential_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_existential_arity T'
         end
  end.

Ltac get_goal_existential_arity :=
  match goal with |- ?T => get_term_existential_arity T end.

(** [exists T1 ... TN] is a shorthand for [exists T1; ...; exists TN].
    It is intended to prove goals of the form [exist X1 .. XN, P].
    If an argument provided is [__] (double underscore), then an
    evar is introduced. [exists T1 .. TN ___] is equivalent to
    [exists T1 .. TN __ __ __] with as many [__] as possible. *)

Tactic Notation "exists_original" constr(T1) :=
  exists T1.
Tactic Notation "exists" constr(T1) :=
  match T1 with
  | ltac_wild => esplit
  | ltac_wilds => repeat esplit
  | _ => exists T1
  end.
Tactic Notation "exists" constr(T1) constr(T2) :=
  exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
  exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1; exists T2; exists T3; exists T4.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1; exists T2; exists T3; exists T4; exists T5.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1; exists T2; exists T3; exists T4; exists T5; exists T6.

(** For compatibility with Coq syntax, [exists T1, .., TN] is also provided. *)

Tactic Notation "exists" constr(T1) "," constr(T2) :=
  exists T1 T2.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) :=
  exists T1 T2 T3 T4.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) :=
  exists T1 T2 T3 T4 T5.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6.

(** Existentials and Conjunctions in Hypotheses *)

(** [unpack] or [unpack H] destructs conjunctions and existentials in
    all or one hypothesis. *)

Ltac unpack_core :=
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists (varname: _), _ |- _ =>
      (* kludge to preserve the name of the quantified variable *)
      let name := fresh varname in
      destruct H as [name ?]
  end.

Ltac unpack_hypothesis H :=
  try match type of H with
  | _ /\ _ =>
      let h1 := fresh "TEMP" in
      let h2 := fresh "TEMP" in
      destruct H as [ h1 h2 ];
      unpack_hypothesis h1;
      unpack_hypothesis h2
  | exists (varname: _), _ =>
      (* kludge to preserve the name of the quantified variable *)
      let name := fresh varname in
      let body := fresh "TEMP" in
      destruct H as [name body];
      unpack_hypothesis body
  end.

Tactic Notation "unpack" :=
  unpack_core.
Tactic Notation "unpack" constr(H) :=
  unpack_hypothesis H.

