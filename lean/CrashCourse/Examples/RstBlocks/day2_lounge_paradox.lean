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

-- camper is a type.
-- If x : camper then x is a camper in the main lounge.
-- singing x is inhabited if x is singing

theorem math_campers_singing_paradox
    (camper : Type)
    (singing : camper → Prop)
    (alice : camper) -- making sure that there is at least one camper in the lounge
    : ∃ x : camper, (singing x → (∀ y : camper, singing y)) := by
  sorry
--END--