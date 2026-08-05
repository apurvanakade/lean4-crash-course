import Mathlib.Tactic

-- landing in ℕ recursion (rather than subtraction) avoids the perils of nat subtraction
def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => n + 1 + f n

example : f 1 = 1 := by
  sorry

example (n : ℕ) : 2 * f n = n * (n + 1) := by
  sorry