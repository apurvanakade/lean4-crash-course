import Mathlib.Tactic

variable (X : Type)

theorem reflexive_of_symmetric_transitive_and_connected
    (r : X → X → Prop)
    (h_symm : ∀ x y : X, r x y → r y x)
    (h_trans : ∀ x y z : X, r x y → r y z → r x z)
    (h_connected : ∀ x, ∃ y, r x y) :
    (∀ x : X, r x x) := by
  sorry