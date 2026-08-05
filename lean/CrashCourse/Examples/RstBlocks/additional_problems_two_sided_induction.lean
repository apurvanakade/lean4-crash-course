import Mathlib.Tactic

example
    (p : ℤ → Prop)
    (p_succ : ∀ n, p n → p (n + 1))
    (p_pred : ∀ n, p n → p (n - 1)) :
    (∀ n, p n) ↔ p 0 := by
  sorry