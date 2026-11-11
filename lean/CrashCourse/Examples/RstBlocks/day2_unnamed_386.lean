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


#check Nat.prime_def
example : Nat.Prime 101 := by
  sorry

-- you will need the definition
-- a ∣ b := (∃ k : ℕ, b = a * k)
example (m a b : ℕ) : m + a ∣ m ^ 2 + (a + b) * m + a * b := by
  sorry

-- ``Nat.prime_def`` is a proof of ``Nat.Prime p ↔ (2 ≤ p ∧ ...)``.
-- Its first component ``Nat.prime_def.1`` is the ``→`` direction,
-- so try ``have h := Nat.prime_def.1 hp`` to get started
example (p : ℕ) (hp : Nat.Prime p) : ¬ (p = 1) := by
  sorry

-- if none of the simplifiers work, try doing ``contrapose!``
-- sometimes the simplifiers need a little help
example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  sorry