import Mathlib.Tactic

-- --------------------------------------------------------------------------
--
-- ``have``
--
--   ``have hp : P`` creates a new goal with target ``P`` and
--   adds ``hp : P`` as a hypothesis to the original goal.
--
-- You'll need the following theorem from the library:
--
-- Nat.dvd_sub' : k ∣ m → k ∣ n → k ∣ m - n
--
--    (Note that you don't need to provide m n k as inputs to dvd_sub'.
--    Lean can infer these from the rest of the expression.
--    More on this tomorrow.)
--
-- Delete the ``sorry`` below and replace it with a legitimate proof.
--
-- --------------------------------------------------------------------------

theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) := by
  sorry