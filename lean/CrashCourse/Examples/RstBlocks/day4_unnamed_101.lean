import Mathlib.Tactic

--BEGIN--
-- Nat.Prime.dvd_of_dvd_pow : p.Prime → p ∣ m ^ n → p ∣ m
lemma two_dvd_of_two_dvd_sq {k : ℕ}
    (hk : 2 ∣ k ^ 2) :
    2 ∣ k := by
  sorry

-- to switch the target from ``P = Q`` to ``Q = P``,
-- use the tactic ``symm``
lemma division_lemma_n {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ n := by
  sorry

lemma div_2 {m n : ℕ} (hnm : 2 * m = 2 * n) : (m = n) := by
  linarith

lemma division_lemma_m {m n : ℕ}
    (hmn : 2 * m ^ 2 = n ^ 2) :
    2 ∣ m := by
  sorry
--END--