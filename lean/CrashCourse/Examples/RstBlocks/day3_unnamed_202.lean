import Mathlib.Tactic

theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) := by
  sorry

-- dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1)
--
-- m ∣ n := ∃ k : ℕ, n = m * k
-- p.Prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)
-- Nat.Prime.one_lt : p.Prime → 1 < p
--
-- n ! := Nat.factorial n
-- Nat.factorial_pos : ∀ (n : ℕ), 0 < n !
-- Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !
--
-- Nat.minFac n := smallest non-trivial factor of n
-- Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime
-- Nat.minFac_pos : ∀ (n : ℕ), 0 < Nat.minFac n
-- Nat.minFac_dvd : ∀ (n : ℕ), Nat.minFac n ∣ n

theorem exists_infinite_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p ≥ n := by
  set p := Nat.minFac (Nat.factorial n + 1) with hp_def
  sorry