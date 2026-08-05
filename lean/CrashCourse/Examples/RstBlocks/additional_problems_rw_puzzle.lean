import Mathlib.Tactic

example
    (p : ℕ → Prop) (n : ℕ) (hn : p n)
    (h8 : ∀ n, p n ↔ p (n + 8))
    (h3 : ∀ n, p (n + 3) ↔ p n) :
    p (n + 1) := by
  sorry