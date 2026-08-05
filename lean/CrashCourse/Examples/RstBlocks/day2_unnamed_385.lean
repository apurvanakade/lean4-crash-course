import Mathlib.Tactic

-- --------------------------------------------------------------------------
--
-- ``norm_num``
--
--   Useful for arithmetic.
--
-- ``ring``
--
--   Useful for basic algebra.
--
-- ``linarith``
--
--   Useful for inequalities.
--
-- ``simp``
--
--   Complex simplifier. Use only to close goals.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

example : 1 > 0 := by
  sorry

example (m a b : ℕ) : m ^ 2 + (a + b) * m + a * b = (m + a) * (m + b) := by
  sorry

example : 101 ∣ 2020 := by
  sorry


#print Nat.Prime
example : Nat.Prime 101 := by
  sorry

-- you will need the definition
-- a ∣ b := (∃ k : ℕ, b = a * k)
example (m a b : ℕ) : m + a ∣ m ^ 2 + (a + b) * m + a * b := by
  sorry

-- try ``unfold Nat.Prime at hp`` to get started
example (p : ℕ) (hp : Nat.Prime p) : ¬ (p = 1) := by
  sorry

-- if none of the simplifiers work, try doing ``contrapose!``
-- sometimes the simplifiers need a little help
example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  sorry