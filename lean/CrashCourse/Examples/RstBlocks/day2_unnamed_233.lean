import Mathlib.Tactic

--BEGIN--

-- --------------------------------------------------------------------------
--
-- ``by_cases``
--
--   If ``P`` is a proposition, then ``by_cases P`` creates two goals,
--     the first with a hypothesis ``hp : P`` and
--     second with a hypothesis ``hp : ¬ P``.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

-- men is a type.
-- x : men means x is a man in the town
-- shaves x y is inhabited if x shaves y

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) := by
  sorry
--END--