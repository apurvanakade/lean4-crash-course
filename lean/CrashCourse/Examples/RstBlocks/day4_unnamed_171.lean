import Mathlib.Tactic

theorem sqrt2_irrational' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
  sorry

-- Assume that everything above this line is true.

--BEGIN--

lemma ne_zero_ge_zero {n : ℕ}
    (hne : n ≠ 0) :
    (0 < n) := by
  contrapose! hne
  sorry

-- Nat.pow_pos : 0 < p → 0 < p ^ n  (n is inferred automatically)
lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n ^ 2) := by
  sorry

lemma cancellation_lemma {k m n : ℕ}
    (hk_pos : 0 < k ^ 2)
    (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) :
    2 * m ^ 2 = n ^ 2 := by
  apply Nat.eq_of_mul_eq_mul_right hk_pos
  ring_nf
  ring_nf at hmn
  linarith [hmn]

--END--