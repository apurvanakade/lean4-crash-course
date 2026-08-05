import Mathlib.Tactic

example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  -- Introduce the hypothesis `¬¬¬P` and the assumption `p : P` we want to contradict.
  intro nnnp p
  -- It suffices to show `¬¬P`.
  apply nnnp
  -- Introduce the hypothesis `¬P` and derive `False`.
  intro np
  -- Apply `¬P` to...
  apply np
  -- ...the term `p : P` we assumed.
  apply p

example (p : ℕ) : p.Prime → p = 2 ∨ p % 2 = 1 := by
  -- This is exactly the mathlib lemma `Nat.Prime.eq_two_or_odd`.
  exact fun a => a.eq_two_or_odd

#check @Nat.Prime.eq_two_or_odd

lemma eq_two_of_even_prime {p : ℕ} (hp : p.Prime) (h_even : Even p) : p = 2 := by
  -- A prime is either `2` or odd.
  rcases hp.eq_two_or_odd with h | h
  · -- If `p = 2`, we're done.
    exact h
  · -- If `p` is odd, this contradicts `p` being even.
    rw [← Nat.not_even_iff] at h
    exact absurd h_even h

lemma even_of_odd_add_odd
    {a b : ℕ} (ha : ¬ Even a) (hb : ¬ Even b) :
    Even (a + b) := by
  -- `a + b` is even iff `a`, `b` are both even or both odd.
  rw [Nat.even_add]
  -- Both are odd (neither is even), so the "iff" holds.
  tauto

lemma one_lt_of_nontrivial_factor
    {b c : ℕ} (hb : b < b * c) :
    1 < c := by
  -- Case on whether `c` is `0`, `1`, or `≥ 2`.
  rcases c with _ | _ | c
  · -- `c = 0` gives `b < 0`, impossible.
    simp at hb
  · -- `c = 1` gives `b < b`, impossible.
    simp at hb
  · -- `c = k + 2 ≥ 2`, so `1 < c`.
    omega

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  omega

lemma nontrivial_product_of_not_prime
    {k : ℕ} (hk : ¬ k.Prime) (two_le_k : 2 ≤ k) :
    ∃ a b, a < k ∧ b < k ∧ 1 < a ∧ 1 < b ∧ a * b = k := by
  -- A non-prime `k ≥ 2` has a factor `a` with `2 ≤ a < k`.
  obtain ⟨a, ha_dvd, ha2, ha_lt⟩ := Nat.exists_dvd_of_not_prime2 two_le_k hk
  -- Unpack the divisibility `a ∣ k` as `k = a * b` for some `b`.
  obtain ⟨b, hb⟩ := ha_dvd
  -- Substituting `k = a * b` into `a < k` gives `a < a * b`.
  have hab : a < a * b := by rw [← hb]; exact ha_lt
  -- From `a < a * b`, `b` must be greater than `1`.
  have hb2 : 1 < b := one_lt_of_nontrivial_factor hab
  -- And `b < k`, since `b < a * b = k` (as `a ≥ 2`).
  have hbk : b < k := by
    rw [hb]
    nlinarith
  -- `a` and `b` are the witnesses we need.
  exact ⟨a, b, ha_lt, hbk, ha2, hb2, hb.symm⟩

theorem three_fac_of_sum_consecutive_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
    (consecutive : ∀ k, p < k → k < q → ¬ k.Prime) :
    ∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 := by
  -- Since `p, q` are primes other than `2`, they're both odd, so their sum is even.
  have h1 : Even (p + q) := by
    apply even_of_odd_add_odd
    · contrapose! p_ne_2; exact eq_two_of_even_prime hp p_ne_2
    · contrapose! q_ne_2; exact eq_two_of_even_prime hq q_ne_2
  -- So `p + q = k + k` for some `k`, i.e. `p + q = 2 * k`.
  obtain ⟨k, hk⟩ := h1
  -- `k` lies strictly between `p` and `q`: from `p + q = k + k` and `p < q`.
  have hpk : p < k := by linarith
  have hkq : k < q := by linarith
  -- So `k` can't be prime.
  have hk' : ¬ k.Prime := consecutive k hpk hkq
  have h2k : 2 ≤ k := by have := hp.two_le; linarith
  -- A non-prime `k ≥ 2` splits as a nontrivial product `b * c`.
  obtain ⟨b, c, hbk, hck, hb1, hc1, hbc⟩ := nontrivial_product_of_not_prime hk' h2k
  -- `2, b, c` are the witnesses we need.
  use 2, b, c
  constructor
  · -- It remains to check `p + q = 2 * b * c`, using `p + q = k + k` and `k = b * c`.
    rw [hk, ← hbc]
    ring
  · -- The three inequalities `2 > 1`, `b > 1`, `c > 1` are immediate.
    exact ⟨by norm_num, hb1, hc1⟩
