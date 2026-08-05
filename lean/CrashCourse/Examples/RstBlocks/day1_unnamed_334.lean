import Mathlib.Tactic

--BEGIN--


-- --------------------------------------------------------------------------
--
-- ``exfalso``
--
--   Changes the target of the current goal to ``False``.
--
-- ``push Not``
--
--   ``push Not`` simplifies negations in the target.
--   You can push negations across a hypothesis ``hp : P`` using
--   ``push Not at hp``.
--
--
-- ``contrapose!``
--
--   If the target of the current goal is  ``P → Q``,
--   then ``contrapose!`` changes the target to  ``¬ Q → ¬ P``.
--
--   If the target of the current goal is ``Q`` and
--   one of the hypotheses is ``hp : P``, then
--   ``contrapose! hp`` changes the target to  ``¬ P`` and
--   changes the hypothesis to ``hp : ¬ Q``.
--
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P := by
  sorry

theorem contrapositive_converse (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  sorry

example (P : Prop) : ¬ P → ¬ ¬ ¬ P := by
  sorry

theorem principle_of_explosion (P Q : Prop) : P → (¬ P → Q) := by
  sorry

--END--