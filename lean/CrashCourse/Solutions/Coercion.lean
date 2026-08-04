import Mathlib.Tactic

-- This is the natural-number version, proved as its own exercise elsewhere;
-- we take it as given here and build the integer/rational versions on top of it.
theorem sqrt2' : ¬ (∃ m n : ℕ, m ≠ 0 ∧ 2 * m ^ 2 = n ^ 2) := by
  sorry

theorem sqrt2 : ¬ (∃ m n : ℤ, m ≠ 0 ∧ 2 * m ^ 2 = n ^ 2) := by
  -- Unpack the existential witness `m, n : ℤ` and the hypotheses about them.
  rintro ⟨m, n, hm, hmn⟩
  -- We'll derive a contradiction with the natural-number version `sqrt2'`.
  apply sqrt2'
  -- Supply `|m|` and `|n|` as the witnesses; `|m| ≠ 0` follows from `m ≠ 0`.
  use m.natAbs, n.natAbs, Int.natAbs_ne_zero.mpr hm
  -- `|m|^2 = m^2` and `|n|^2 = n^2` once coerced back to ℤ, so we can rewrite `hmn`...
  have m1 := Int.natAbs_pow_two m
  have n1 := Int.natAbs_pow_two n
  rw [← m1, ← n1] at hmn
  -- ...and then push the equation down from ℤ to ℕ.
  exact_mod_cast hmn

example : ¬ (∃ q : ℚ, 2 = q * q) := by
  -- Unpack the witness `q` and the hypothesis `2 = q * q`.
  rintro ⟨q, key⟩
  -- Cross-multiplying `2 = q * q` (viewed as fractions) gives an equation of numerators/denominators.
  have h := Rat.eq_iff_mul_eq_mul.mp key
  -- `2 : ℚ` has denominator `1` and numerator `2`.
  have triv1 : (2 : ℚ).den = 1 := by norm_num
  have triv2 : (2 : ℚ).num = 2 := by norm_num
  -- Rewrite `h` using these facts, plus the formulas for `(q * q).den` and `(q * q).num`.
  rw [triv1, triv2, Rat.mul_self_den, Rat.mul_self_num] at h
  -- Normalize the casts so `h` is a clean equation in `ℤ`.
  push_cast at h
  -- We'll derive a contradiction with the integer version `sqrt2`.
  apply sqrt2
  -- Supply `q.den` and `q.num` as the witnesses; the two remaining goals are proved separately.
  use (q.den : ℤ), q.num
  constructor
  · -- `q.den ≠ 0`, cast to ℤ.
    exact_mod_cast q.den_nz
  · -- The equation `2 * q.den ^ 2 = q.num ^ 2` follows from `h` by linear arithmetic.
    nlinarith [h]

example (q : ℚ) : q.den ≠ 0 :=
  q.den_nz

example (m : ℤ) : m ^ 2 = (m.natAbs : ℤ) ^ 2 :=
  (Int.natAbs_pow_two m).symm
