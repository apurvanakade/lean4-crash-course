import Mathlib.Tactic

namespace Day2

section barber
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) := by
  intro h
  -- Specialize the barber hypothesis to the barber himself.
  have hb := h barber
  -- Either the barber shaves himself or he doesn't; both are contradictory.
  by_cases hs : shaves barber barber
  · exact (hb.mp hs) hs
  · exact hs (hb.mpr hs)

end barber

theorem math_campers_singing_paradox
    (camper : Type)
    (singing : camper → Prop)
    (alice : camper) :
    ∃ x : camper, (singing x → (∀ y : camper, singing y)) := by
  -- Either everyone sings or somebody doesn't.
  by_cases h : ∀ y, singing y
  · -- Everyone sings, so any camper works (the conclusion holds outright).
    exact ⟨alice, fun _ => h⟩
  · -- Someone isn't singing; take `x` to be that camper, so `singing x` is false
    -- and the implication holds vacuously.
    push Not at h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, fun hs => absurd hs hx⟩

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  obtain hp | hq := h
  · right
    exact hp
  · left
    exact hq

example (P Q R : Prop) : P ∧ False ↔ False := by
  constructor
  · intro h
    exact h.2
  · intro h
    exfalso
    exact h

theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q := by
  intro ⟨hp, hnp⟩
  exfalso
  exact hnp hp

section reflexive
variable (X : Type)

theorem reflexive_of_symmetric_transitive_and_connected
    (r : X → X → Prop)
    (h_symm : ∀ x y : X, r x y → r y x)
    (h_trans : ∀ x y z : X, r x y → r y z → r x z)
    (h_connected : ∀ x, ∃ y, r x y) :
    (∀ x : X, r x x) := by
  intro x
  -- `x` is related to some `y`; symmetry gives `r y x`, transitivity `r x x`.
  obtain ⟨y, hxy⟩ := h_connected x
  exact h_trans x y x hxy (h_symm x y hxy)

end reflexive

example : 1 > 0 := by
  norm_num

example (m a b : ℕ) : m ^ 2 + (a + b) * m + a * b = (m + a) * (m + b) := by
  ring

example : 101 ∣ 2020 := by
  norm_num  -- `decide` also works

example : Nat.Prime 101 := by
  norm_num

example (m a b : ℕ) : m + a ∣ m ^ 2 + (a + b) * m + a * b := by
  -- `m ^ 2 + (a + b) * m + a * b = (m + a) * (m + b)`, so the quotient is `m + b`.
  use m + b
  ring

example (p : ℕ) (hp : Nat.Prime p) : ¬ (p = 1) := by
  -- A prime is at least `2`, so it is not `1`.
  have h := Nat.prime_def.1 hp
  omega

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  constructor
  · intro h
    omega
  · intro h
    -- `contrapose!` turns `n ≠ 0` into `¬ 0 < n`, which `omega` can use.
    contrapose! h
    omega

end Day2
