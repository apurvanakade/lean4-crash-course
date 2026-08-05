import Mathlib.Tactic

variable {R : Type*} [CommRing R]

-- find the matching lemma in mathlib
example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  sorry

-- now redo it "by hand", by induction on n
example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  sorry