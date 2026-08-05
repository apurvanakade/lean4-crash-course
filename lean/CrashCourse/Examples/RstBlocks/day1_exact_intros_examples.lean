-- --------------------------------------------------------------------------
--
-- ``exact``
--
--   If ``P`` is the target of the current goal and
--   ``hp`` is a term of type ``P``, then
--   ``exact hp`` will close the goal.
--
--
-- ``intro``
--
--   If the target of the current goal is a function ``P → Q``, then
--   ``intro hp`` will produce a hypothesis
--   ``hp : P`` and change the target to  ``Q``.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

theorem tautology (P : Prop) (hp : P) : P := by
  sorry

theorem tautology' (P : Prop) : P → P := by
  sorry

example (P Q : Prop) : (P → (Q → P)) := by
  sorry

-- Can you find two different ways of proving the following?
example (P Q : Prop) : ((Q → P) → (Q → P)) := by
  sorry