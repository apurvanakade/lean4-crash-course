import Mathlib.Tactic
open Function

namespace Day3

example (a b c d : ℕ)
    (hyp : c = d * a + b)
    (hyp' : b = a * d) :
    c = 2 * (a * d) := by
  rw [hyp, hyp', mul_comm d a]
  -- Goal: `a * d + a * d = 2 * (a * d)`.
  ring

example (a b c d : ℕ)
    (hyp : c = b * a - d)
    (hyp' : d = a * b) :
    c = 0 := by
  -- Goal after rewriting: `a * b - a * b = 0`.
  rw [hyp, hyp', mul_comm b a, Nat.sub_self]

section surjective
variable (X Y Z : Type)
variable (f : X → Y) (g : Y → Z)

example
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  -- Pull `z` back through `g` to some `y`, then through `f` to some `x`.
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [comp_apply, hx, hy]

example
    (hgf : Surjective (g ∘ f)) :
    Surjective g := by
  intro z
  -- If `g (f x) = z`, then `f x` is the preimage of `z` under `g`.
  obtain ⟨x, hx⟩ := hgf z
  use f x
  exact hx

end surjective

theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) := by
  intro h1 h2
  -- `p` divides the difference `(a + 1) - a`...
  have h3 := Nat.dvd_sub h2 h1
  -- ...which is `1`.
  have h4 : a + 1 - a = 1 := by omega
  rw [h4] at h3
  exact h3

theorem exists_infinite_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p ≥ n := by
  set p := Nat.minFac (Nat.factorial n + 1) with hp_def
  -- `n! + 1 ≥ 2`, so `n! + 1 ≠ 1` and its smallest factor `p` is prime.
  have h_fact_pos := Nat.factorial_pos n
  have pp : p.Prime := Nat.minFac_prime (by omega)
  use p
  constructor
  · exact pp
  · -- Suppose `p < n`.
    by_contra h
    push Not at h
    -- Then `p ∣ n!`, as `p` is one of the factors `1, ..., n`;
    have hp1 : p ∣ Nat.factorial n := Nat.dvd_factorial pp.pos h.le
    -- and `p ∣ n! + 1` by definition of `p`.
    have hp2 : p ∣ Nat.factorial n + 1 := Nat.minFac_dvd _
    -- So `p ∣ 1`, which is impossible for a prime.
    have hp3 := dvd_sub_one hp1 hp2
    exact pp.not_dvd_one hp3

end Day3
