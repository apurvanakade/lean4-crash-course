import Mathlib.Tactic

theorem sqrt2_irrational' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
  sorry

lemma ne_zero_ge_zero {n : ℕ}
    (hne : n ≠ 0) :
    (0 < n) := by
  contrapose! hne
  sorry

lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n ^ 2) := by
  sorry

lemma cancellation_lemma {k m n : ℕ}
    (hk_pos : 0 < k ^ 2)
    (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) :
    2 * m ^ 2 = n ^ 2 := by
  sorry

-- Assume that everything above this line is true.

--BEGIN--

-- Nat.gcd_pos_of_pos_left : 0 < m → 0 < Nat.gcd m n
-- Nat.gcd_pos_of_pos_right : 0 < n → 0 < Nat.gcd m n
-- Nat.exists_coprime : ∀ (m n : ℕ), ∃ m' n', m'.Coprime n' ∧ m = m' * m.gcd n ∧ n = n' * m.gcd n

theorem wlog_coprime :
    (∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0) →
    (∃ (m' n' : ℕ), 2 * m' ^ 2 = n' ^ 2 ∧ m'.Coprime n') := by
  rintro ⟨m, n, hmn, hme0⟩
  set k := m.gcd n with hk
  -- might be useful to declutter
  -- you can replace all the ``m.gcd n`` with ``k`` using ``rw [← hk]`` if needed
  sorry

theorem sqrt2_irrational'' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0 := by
  sorry

--END--