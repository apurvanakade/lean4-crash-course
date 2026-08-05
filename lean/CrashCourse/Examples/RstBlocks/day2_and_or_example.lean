import Mathlib.Tactic

--BEGIN--


-- --------------------------------------------------------------------------
--
-- ``obtain``
--
--   ``obtain`` is a general tactic that breaks up complicated terms.
--   If ``hpq`` is a term of type ``P ∧ Q`` or ``P ↔ Q``, then use
--   ``obtain ⟨hp, hq⟩ := hpq``.
--   If ``hpq`` is a term of type ``P ∨ Q``, then use
--   ``obtain hp | hq := hpq``.
--
-- ``constructor``
--
--   If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, then use
--   ``constructor``.
--
-- ``left``/``right``
--
--   If the target of the current goal is ``P ∨ Q``, then use
--   either ``left`` or ``right`` (choose wisely).
--
-- ``exfalso``
--
--   Changes the target of the current goal to ``False``.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

example (P Q R : Prop) : P ∧ False ↔ False := by
  sorry

theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q := by
  sorry

--END--