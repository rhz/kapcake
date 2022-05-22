From KapCake Require Export LibTactics.

(* These tactics do the following.
   1. Unfold hypotheses H, H1, H2
      of the form `In (x, y) ((0, 1) :: xs)`
      to `(0, 1) = (x, y) \/ ...` using `simpl`.
   2. Split the generated disjunctions using `branches`.
   3. Solve the generated subgoals by substituting
      `x = 0`, `y = 1` and then using the tactic `tac`
      or by finding False in the hypotheses.
 *)
Tactic Notation "pairsInList" hyp(H) "then_" tactic(tac) :=
  simpl in H; branches H; solve [ injects H; tac | false ].
Tactic Notation "pairsInList" hyp(H1) "," constr(H2)
  "then_" tactic(tac) :=
  simpl in H1, H2; branches H1; branches H2;
  solve [ injects H1; injects H2; tac | false_invert | false ].

