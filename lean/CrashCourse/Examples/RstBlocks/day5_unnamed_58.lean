import Mathlib.Tactic

theorem sqrt2_irrational_nat :
    ¬ ∃ (m n : ℕ), 2 * (m * m) = (n * n) ∧ m ≠ 0 := by
  sorry

-- Assume the above theorem

lemma num_2 : (2 : ℚ).num = 2 := by
  norm_num

lemma den_2 : (2 : ℚ).den = 1 := by
  norm_num

-- q.den = denominator of q (valued in ℕ)
-- q.num = numerator of q (valued in ℤ)
--
-- for integer m,
-- m.natAbs = absolute value of m (valued in ℕ)
--
-- Rat.mul_self_den : ∀ (q : ℚ), (q * q).den = q.den * q.den
-- Rat.mul_self_num : ∀ (q : ℚ), (q * q).num = q.num * q.num
-- Int.natAbs_mul_self' : ∀ (a : ℤ), ↑(a.natAbs) * ↑(a.natAbs) = a * a
-- Rat.den_nz : ∀ (q : ℚ), q.den ≠ 0

-- Use ``simp at hp`` (or, interactively, ``simp? at hp``) to commute
-- products with coercions. See the goal window!

theorem sqrt2_irrational :
    ¬ (∃ q : ℚ, 2 = q * q) := by
  rintro ⟨q, key⟩
  have clear_denom := Rat.eq_iff_mul_eq_mul.mp key
  sorry