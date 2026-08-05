import Mathlib.Tactic

lemma even_or_odd (n : ℕ) :
    (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  sorry