import Mathlib.Tactic

theorem reflexive_of_symmetric_and_transitive (r : ℕ → ℕ → Prop)
    (h_symm : Std.Symm r) (h_trans : IsTrans ℕ r)
    (h_connected : ∀ x, ∃ y, r x y) :
    Std.Refl r where
  refl x := by
    sorry