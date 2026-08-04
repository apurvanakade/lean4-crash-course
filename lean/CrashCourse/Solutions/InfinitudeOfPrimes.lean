import Mathlib.Tactic

theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ p.Prime := by
  -- Let `p` be the smallest prime factor of `n! + 1`; this is the prime we'll produce.
  set p := Nat.minFac (Nat.factorial n + 1) with hp_def
  -- `n!` is always positive, so `n! + 1 ≥ 2`.
  have h_fact_pos := Nat.factorial_pos n
  -- `n! + 1 ≠ 1` (since `n! + 1 ≥ 2`), so its smallest factor `p` is genuinely prime.
  have pp : p.Prime := Nat.minFac_prime (by omega)
  -- `p` is our witness; the remaining goals (`p ≥ n` and `p.Prime`) are proved as subproofs.
  use p
  constructor
  · -- Suppose, for contradiction, that `p < n`.
    by_contra h
    push Not at h
    -- Then `p ≤ n`, so `p` divides `n!` (it's one of the factors `1, 2, ..., n`).
    have hp1 : p ∣ Nat.factorial n := Nat.dvd_factorial pp.pos h.le
    -- `p` divides `n! + 1` too, since `p` was defined as a factor of `n! + 1`.
    have hp2 : p ∣ Nat.factorial n + 1 := Nat.minFac_dvd _
    -- A number dividing both `n!` and `n! + 1` must divide their difference, `1`.
    have hp3 : p ∣ 1 := (Nat.dvd_add_right hp1).mp hp2
    -- But no prime divides `1` — contradiction.
    exact pp.not_dvd_one hp3
  · exact pp
