import Mathlib.Tactic

lemma two_dvd_of_two_dvd_sq {n : ℕ} (hn : 2 ∣ n ^ 2) : 2 ∣ n := by
  -- `2` is prime, and a prime dividing `n ^ 2` must divide `n`.
  apply Nat.Prime.dvd_of_dvd_pow
  · exact Nat.prime_two
  · exact hn

lemma two_dvd_of_two_dvd_sq' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ n := by
  -- Reduce to the previous lemma, using `n ^ 2 = 2 * m ^ 2` to show `2 ∣ n ^ 2`.
  apply two_dvd_of_two_dvd_sq
  exact ⟨m ^ 2, hmn.symm⟩

example (a b c : ℕ) (hc : 0 < c) (h : c * a = c * b) : a = b := by
  -- Cancel the common nonzero factor `c` on both sides.
  rwa [Nat.mul_right_inj hc.ne'] at h

lemma two_dvd_of_two_dvd_sq'' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ m := by
  -- Reduce to showing `2 ∣ m ^ 2`.
  apply two_dvd_of_two_dvd_sq
  -- Since `2 ∣ n`, write `n = 2 * k`.
  obtain ⟨k, hk⟩ := two_dvd_of_two_dvd_sq' hmn
  -- `k ^ 2` will be the witness; it remains to check `m ^ 2 = 2 * k ^ 2`.
  use k ^ 2
  -- Substitute `n = 2 * k` into `2 * m ^ 2 = n ^ 2`.
  rw [hk] at hmn
  -- Cancel the factor of `2` from both sides of the goal.
  rw [← Nat.mul_right_inj (by norm_num : (2:ℕ) ≠ 0)]
  -- Normalize both sides and finish by linear arithmetic.
  ring_nf
  ring_nf at hmn
  linarith [hmn]

lemma gcd_div_left (a b : ℕ) : (Nat.gcd a b) ∣ a :=
  Nat.gcd_dvd_left a b

lemma gcd_div_right (a b : ℕ) : (Nat.gcd a b) ∣ b :=
  Nat.gcd_dvd_right a b

lemma eq_zero_of_sq_eq_zero (m : ℕ) (hm : m ^ 2 = 0) : m = 0 := by
  simpa using hm

lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m ^ 2 = 0 ↔ m = 0 := by
  constructor
  · apply eq_zero_of_sq_eq_zero
  · intro h; rw [h]; ring

lemma coprime_of_div_gcd
    (m n m' n' k : ℕ)
    (hk : k = Nat.gcd m n)
    (hmk : m = k * m')
    (hnk : n = k * n')
    (hm : 0 < m)
    (_hn : 0 < n) :
    Nat.Coprime m' n' := by
  -- `gcd (k * m') (k * n') = k * gcd m' n'` in general.
  have key := Nat.gcd_mul_left k m' n'
  -- Rewrite using `m = k * m'`, `n = k * n'`, `k = gcd m n` to get `k = k * gcd m' n'`.
  rw [← hmk, ← hnk, ← hk] at key
  -- `k` itself is positive, since it's the gcd of the positive number `m` (and `n`).
  have hk_pos : 0 < k := by rw [hk]; exact Nat.gcd_pos_of_pos_left n hm
  unfold Nat.Coprime
  -- Rewrite `key` as `k * gcd m' n' = k * 1`.
  have heq : k * Nat.gcd m' n' = k * 1 := by rw [← key]; ring
  -- Cancel the nonzero factor `k` to conclude `gcd m' n' = 1`.
  exact Nat.eq_of_mul_eq_mul_left hk_pos heq

lemma wlog_nonzero {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : n ≠ 0 := by
  -- Suppose instead `n = 0`.
  intro hn
  subst hn
  -- Then `2 * m ^ 2 = 0`, so `m ^ 2 = 0`.
  have hm2 : m ^ 2 = 0 := by nlinarith
  -- But that forces `m = 0`, contradicting `hm`.
  exact hm ((sq_eq_zero_iff_eq_zero m).mp hm2)

lemma gcd_ne_zero {m n : ℕ} (hm : m ≠ 0) (_hn : n ≠ 0) : Nat.gcd m n ≠ 0 := by
  -- `gcd m n > 0` whenever `m > 0`.
  have := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  exact this.ne'

lemma ne_zero_of_mul_ne_zero {m k m' : ℕ}
    (hm : m ≠ 0)
    (hkm : m = k * m') :
    m' ≠ 0 := by
  -- Suppose instead `m' = 0`; then `m = k * 0 = 0`, contradicting `hm`.
  contrapose! hm
  rw [hkm, hm]
  ring

lemma wlog_coprime_aux {m n k : ℕ}
    (hmn : 2 * (k * m) ^ 2 = (k * n) ^ 2)
    (hk : k ≠ 0) :
    2 * m ^ 2 = n ^ 2 := by
  -- `k ^ 2` is a nonzero common factor we can cancel.
  have hk2 : k ^ 2 ≠ 0 := by positivity
  -- Rewrite the hypothesis as `k ^ 2 * (2 * m ^ 2) = k ^ 2 * n ^ 2`.
  have heq : k ^ 2 * (2 * m ^ 2) = k ^ 2 * n ^ 2 := by ring_nf; ring_nf at hmn; linarith
  -- Cancel `k ^ 2` from both sides.
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk2) heq

lemma wlog_coprime {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) :
    ∃ m' n', m' ≠ 0 ∧ 2 * m' ^ 2 = n' ^ 2 ∧ Nat.Coprime m' n' := by
  -- Let `k` be the gcd of `m` and `n`, and divide it out.
  set k := m.gcd n with hk_def
  have hn : n ≠ 0 := wlog_nonzero hm hmn
  have hk : k ≠ 0 := gcd_ne_zero hm hn
  have hkm : k ∣ m := gcd_div_left m n
  have hkn : k ∣ n := gcd_div_right m n
  -- Write `m = k * m'` and `n = k * n'`.
  obtain ⟨m', hkm'⟩ := hkm
  obtain ⟨n', hkn'⟩ := hkn
  -- `m'` and `n'` are the witnesses; the three remaining facts are proved separately.
  use m', n'
  constructor
  · -- `m' ≠ 0`, since `m = k * m' ≠ 0`.
    exact ne_zero_of_mul_ne_zero hm hkm'
  · constructor
    · -- `2 * m' ^ 2 = n' ^ 2` follows from `hmn` after substituting `m = k * m'`, `n = k * n'`
      -- and cancelling the common factor `k ^ 2`.
      rw [hkm', hkn'] at hmn
      exact wlog_coprime_aux hmn hk
    · -- `m'` and `n'` are coprime, since dividing `m, n` by their gcd `k` leaves no common factor.
      exact coprime_of_div_gcd m n m' n' k hk_def hkm' hkn'
        (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma not_coprime_of_common_factor {m n k : ℕ}
    (hk : 1 < k) (_hm : m ≠ 0) (_hn : n ≠ 0) (hmk : k ∣ m) (hnk : k ∣ n) :
    ¬ Nat.Coprime n m := by
  -- Suppose instead `n` and `m` were coprime.
  intro hcop
  -- Then `k`, dividing both, must divide `gcd n m`.
  have hdvd := Nat.dvd_gcd hnk hmk
  unfold Nat.Coprime at hcop
  -- But `gcd n m = 1` (that's what coprimality means), so `k ∣ 1`.
  rw [hcop] at hdvd
  -- A divisor of `1` is at most `1`, contradicting `1 < k`.
  have := Nat.le_of_dvd (by norm_num) hdvd
  exact absurd (hk.trans_le this) (lt_irrefl 1)

lemma sqrt2_irrational_aux {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : False := by
  -- Replace `m, n` with the coprime reduced pair `m', n'` satisfying the same equation.
  obtain ⟨m', n', hm', hmn', hcop⟩ := wlog_coprime hm hmn
  -- But `2` divides both `m'` and `n'` (from `2 * m' ^ 2 = n' ^ 2`), contradicting coprimality.
  apply not_coprime_of_common_factor (k := 2) (by norm_num) hm' (wlog_nonzero hm' hmn')
    (two_dvd_of_two_dvd_sq'' hmn') (two_dvd_of_two_dvd_sq' hmn')
  exact hcop.symm

theorem sqrt2_irrational :
    ¬ ∃ p q : ℕ, p ≠ 0 ∧ 2 * p ^ 2 = q ^ 2 := by
  -- Unpack the witnesses and hypotheses, then derive `False`.
  rintro ⟨p, q, hp, hpq⟩
  exact sqrt2_irrational_aux hp hpq
