import Mathlib.Tactic

-- (a) an even prime must be 2
lemma eq_two_of_even_prime {p : ℕ} (hp : p.Prime) (h_even : Even p) : p = 2 := by
  sorry

-- (b) a sum of two odd numbers is even
lemma even_of_odd_add_odd
    {a b : ℕ} (ha : ¬ Even a) (hb : ¬ Even b) :
    Even (a + b) := by
  sorry

-- (c) if b < b * c, then c is at least 2
lemma one_lt_of_nontrivial_factor
    {b c : ℕ} (hb : b < b * c) :
    1 < c := by
  sorry

-- (d) a composite k ≥ 2 splits as a product of two smaller factors, each > 1
lemma nontrivial_product_of_not_prime
    {k : ℕ} (hk : ¬ k.Prime) (two_le_k : 2 ≤ k) :
    ∃ a b, a < k ∧ b < k ∧ 1 < a ∧ 1 < b ∧ a * b = k := by
  sorry

-- (e) the main theorem
theorem three_fac_of_sum_consecutive_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
    (consecutive : ∀ k, p < k → k < q → ¬ k.Prime) :
    ∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 := by
  sorry