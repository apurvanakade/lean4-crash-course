import Mathlib.Tactic

lemma two_dvd_of_two_dvd_sq {k : ℕ}
    (hk : 2 ∣ k ^ 2) :
    2 ∣ k := by
  sorry

lemma division_lemma_n {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ n := by
  sorry

lemma division_lemma_m {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ m := by
  sorry

-- Assume that everything above this line is true.

--BEGIN--

-- If ``1 < d``, ``d ∣ m``, and ``d ∣ n``, then ``d ∣ Nat.gcd m n`` (via
-- ``Nat.dvd_gcd``), and since ``m.Coprime n`` means ``Nat.gcd m n = 1``,
-- this contradicts ``1 < d``.

theorem sqrt2_irrational' :
    ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
  rintro ⟨m, n, hmn, h_cop⟩
  -- rintro lets you destructure the hypothesis as you introduce it
  -- you get the brackets by typing ``\langle`` and ``\rangle``
  sorry

--END--