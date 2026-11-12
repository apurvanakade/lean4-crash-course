import Mathlib.Tactic

namespace Day4

lemma two_dvd_of_two_dvd_sq {k : ℕ}
    (hk : 2 ∣ k ^ 2) :
    2 ∣ k := by
  exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hk

lemma division_lemma_n {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ n := by
  -- `n ^ 2 = 2 * m ^ 2` is divisible by `2`.
  apply two_dvd_of_two_dvd_sq
  use m ^ 2
  symm
  exact hmn

lemma div_2 {m n : ℕ} (hnm : 2 * m = 2 * n) : (m = n) := by
  linarith

lemma division_lemma_m {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ m := by
  -- Write `n = 2 * k`; then `2 * m ^ 2 = 4 * k ^ 2`, so `m ^ 2 = 2 * k ^ 2`.
  obtain ⟨k, hk⟩ := division_lemma_n hmn
  apply two_dvd_of_two_dvd_sq
  use k ^ 2
  rw [hk] at hmn
  apply div_2
  -- the goal is `2 * m ^ 2 = 2 * (2 * k ^ 2)`; rewrite its left side using `hmn`
  rw [hmn]
  ring

theorem sqrt2_irrational' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
  rintro ⟨m, n, hmn, h_cop⟩
  -- `2` divides both `m` and `n`, hence their gcd, which is `1`.
  have h2m := division_lemma_m hmn
  have h2n := division_lemma_n hmn
  have h2 := Nat.dvd_gcd h2m h2n
  rw [h_cop] at h2
  -- `2 ∣ 1` is absurd.
  omega

lemma ne_zero_ge_zero {n : ℕ}
    (hne : n ≠ 0) :
    (0 < n) := by
  contrapose! hne
  omega

lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n ^ 2) := by
  exact Nat.pow_pos hne

lemma cancellation_lemma {k m n : ℕ}
    (hk_pos : 0 < k ^ 2)
    (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) :
    2 * m ^ 2 = n ^ 2 := by
  apply Nat.eq_of_mul_eq_mul_right hk_pos
  -- `ring` can show that both sides are the two sides of `hmn` in disguise
  calc 2 * m ^ 2 * k ^ 2 = 2 * (m * k) ^ 2 := by ring
    _ = (n * k) ^ 2 := hmn
    _ = n ^ 2 * k ^ 2 := by ring

theorem wlog_coprime :
    (∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0) →
    (∃ (m' n' : ℕ), 2 * m' ^ 2 = n' ^ 2 ∧ m'.Coprime n') := by
  rintro ⟨m, n, hmn, hme0⟩
  set k := m.gcd n with hk
  -- `k > 0`, since `m > 0`.
  have hm_pos : 0 < m := ne_zero_ge_zero hme0
  have hk_pos : 0 < k := Nat.gcd_pos_of_pos_left n hm_pos
  -- Divide out the gcd: `m = m' * k` and `n = n' * k` with `m'`, `n'` coprime.
  obtain ⟨m', n', hcop, hm, hn⟩ := Nat.exists_coprime m n
  refine ⟨m', n', ?_, hcop⟩
  rw [← hk] at hm hn
  rw [hm, hn] at hmn
  -- Cancel the common factor `k ^ 2`.
  apply cancellation_lemma (ge_zero_sq_ge_zero hk_pos)
  exact hmn

theorem sqrt2_irrational'' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0 := by
  -- A solution with `m ≠ 0` yields a coprime one, contradicting `sqrt2_irrational'`.
  intro h
  exact sqrt2_irrational' (wlog_coprime h)

end Day4
