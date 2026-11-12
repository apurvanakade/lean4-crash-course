import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import CrashCourse.Solutions.Day4

namespace Day5

class CyclicGroup (G : Type*) extends Group G where
  has_generator : ∃ g : G, ∀ x : G, ∃ n : ℤ, x = g ^ n

lemma mul_comm_of_cyclic
    {G : Type*}
    [hc : CyclicGroup G] :
    ∀ a b : G, a * b = b * a := by
  have has_generator := hc.has_generator
  -- Let `h` be a generator.
  obtain ⟨h, hh⟩ := has_generator
  intro a b
  -- Write `a = h ^ m` and `b = h ^ n`.
  obtain ⟨m, hm⟩ := hh a
  obtain ⟨n, hn⟩ := hh b
  -- Then both products are `h ^ (m + n)` (resp. `h ^ (n + m)`).
  rw [hm, hn, ← zpow_add, ← zpow_add, add_comm]

-- The exercise's `ℕ` statement, from the result of day 4.
theorem sqrt2_irrational_nat :
    ¬ ∃ (m n : ℕ), 2 * (m * m) = (n * n) ∧ m ≠ 0 := by
  rintro ⟨m, n, h, hm⟩
  apply Day4.sqrt2_irrational''
  exact ⟨m, n, by rw [pow_two, pow_two]; exact h, hm⟩

lemma num_2 : (2 : ℚ).num = 2 := by
  norm_num

lemma den_2 : (2 : ℚ).den = 1 := by
  norm_num

theorem sqrt2_irrational :
    ¬ (∃ q : ℚ, 2 = q * q) := by
  rintro ⟨q, key⟩
  -- Clear denominators in `2 = q * q`.
  have clear_denom := Rat.eq_iff_mul_eq_mul.mp key
  rw [den_2, num_2, Rat.mul_self_den, Rat.mul_self_num] at clear_denom
  -- Push the coercions to get `2 * (q.den * q.den) = q.num * q.num` in `ℤ`.
  push_cast at clear_denom
  rw [mul_one] at clear_denom
  -- This contradicts the `ℕ` version, with `m = q.den` and `n = |q.num|`.
  apply sqrt2_irrational_nat
  refine ⟨q.den, q.num.natAbs, ?_, q.den_nz⟩
  -- `↑|num| * ↑|num| = num * num`, so we can replace `num * num` by it.
  rw [← Int.natAbs_mul_self' q.num] at clear_denom
  norm_cast at clear_denom

-- An alternative route: pass through `ℤ` first.

theorem sqrt2_int : ¬ (∃ m n : ℤ, m ≠ 0 ∧ 2 * m ^ 2 = n ^ 2) := by
  -- Unpack the witnesses `m, n : ℤ` and the hypotheses about them.
  rintro ⟨m, n, hm, hmn⟩
  -- We'll derive a contradiction with the `ℕ` version.
  apply Day4.sqrt2_irrational''
  -- Use `|m|` and `|n|` as witnesses; `|m| ≠ 0` follows from `m ≠ 0`.
  use m.natAbs, n.natAbs
  refine ⟨?_, Int.natAbs_ne_zero.mpr hm⟩
  -- `|m| ^ 2 = m ^ 2` and `|n| ^ 2 = n ^ 2` once coerced back to ℤ.
  have m1 := Int.natAbs_pow_two m
  have n1 := Int.natAbs_pow_two n
  rw [← m1, ← n1] at hmn
  -- Push the equation down from ℤ to ℕ.
  norm_cast at hmn

example : ¬ (∃ q : ℚ, 2 = q * q) := by
  rintro ⟨q, key⟩
  -- Cross-multiplying `2 = q * q` gives an equation of numerators/denominators.
  have h := Rat.eq_iff_mul_eq_mul.mp key
  rw [den_2, num_2, Rat.mul_self_den, Rat.mul_self_num] at h
  push_cast at h
  -- Supply `q.den` and `q.num` as witnesses for the integer version.
  apply sqrt2_int
  use (q.den : ℤ), q.num
  constructor
  · -- `q.den ≠ 0`, cast to ℤ.
    norm_cast
    exact q.den_nz
  · -- `2 * q.den ^ 2 = q.num ^ 2` follows from `h` by linear arithmetic.
    linarith

end Day5
