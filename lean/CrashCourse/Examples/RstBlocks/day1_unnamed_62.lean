import Mathlib.Tactic

theorem fermats_last_theorem
    (n : ℕ)
    (n_gt_2 : n > 2) :
    ¬ (∃ x y z : ℕ, (x ^ n + y ^ n = z ^ n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0)) := by
  sorry