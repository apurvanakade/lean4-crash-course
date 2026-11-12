import Mathlib.Tactic

namespace AdditionalProblems

section rw_puzzle

-- Deduce `p (n + 1)` from `p n`, using the two `iff`s `h8` and `h3`.
example
    (p : ℕ → Prop) (n : ℕ) (hn : p n)
    (h8 : ∀ n, p n ↔ p (n + 8))
    (h3 : ∀ n, p (n + 3) ↔ p n) :
    p (n + 1) := by
  -- `p n` is equivalent to `p (n + 3)`, so we can walk `hn` up by `3` at a time...
  rw [← h3] at hn
  -- ...three times, turning `p n` into `p (n + 9)`...
  rw [← h3] at hn
  rw [← h3] at hn
  -- ...and `p (n + 9) = p ((n + 1) + 8)` is equivalent to `p (n + 1)` via `h8`.
  rw [h8]
  exact hn

end rw_puzzle

section fin_zero_ne_one

example : Fin 0 ≠ Fin 1 := by
  -- `Fin 1` is inhabited (e.g. by `0`).
  have : ∃ b : Fin 1, True := ⟨0, trivial⟩
  -- Suppose instead `Fin 0 = Fin 1`.
  intro h
  -- Then `Fin 0` is also inhabited.
  rw [← h] at this
  -- But `Fin 0` has no elements — contradiction.
  obtain ⟨k, _⟩ := this
  exact k.elim0

end fin_zero_ne_one

section reflexive_of_symmetric_and_transitive

-- A relation that's symmetric, transitive, and serial (every element relates to something) is reflexive.
theorem reflexive_of_symmetric_and_transitive (r : ℕ → ℕ → Prop)
    (h_symm : Std.Symm r) (h_trans : IsTrans ℕ r)
    (h_connected : ∀ x, ∃ y, r x y) :
    Std.Refl r where
  refl x := by
    -- `x` is related to some `y`.
    obtain ⟨y, hy⟩ := h_connected x
    -- Symmetry gives `y` related to `x`; transitivity chains `x r y r x` into `x r x`.
    exact h_trans.trans x y x hy (h_symm.symm x y hy)

end reflexive_of_symmetric_and_transitive

section even_or_odd

lemma even_or_odd (n : ℕ) :
    (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  induction n with
  | zero =>
    -- `0 = 2 * 0` is even.
    left; exact ⟨0, by simp⟩
  | succ d hd =>
    -- Case on whether `d` (the previous number) was even or odd.
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := hd
    · -- If `d = 2 * k`, then `d + 1 = 2 * k + 1` is odd.
      right; exact ⟨k, by rw [hk]⟩
    · -- If `d = 2 * k + 1`, then `d + 1 = 2 * (k + 1)` is even.
      left; exact ⟨k + 1, by rw [hk]; ring⟩

end even_or_odd

section two_sided_induction

-- Two-sided induction on ℤ, splitting into the nonnegative and negative
-- cases via `Int.ofNat`/`Int.negSucc`.
example
    (p : ℤ → Prop)
    (p_succ : ∀ n, p n → p (n + 1))
    (p_pred : ∀ n, p n → p (n - 1)) :
    (∀ n, p n) ↔ p 0 := by
  -- `p` holding at `n` is equivalent to `p` holding at `n + 1` (using both `p_succ` and `p_pred`).
  have key1 : ∀ n, p n ↔ p (n + 1) := by
    intro n
    constructor
    · intro h
      exact p_succ n h
    · intro h
      have := p_pred (n + 1) h
      simpa using this
  constructor
  · -- The forward direction is immediate: specialize `∀ n, p n` at `n = 0`.
    intro h
    exact h 0
  · -- For the converse, we induct outward from `0` in both directions over `ℤ`.
    intro h n
    -- Split `n` into the nonnegative case `Int.ofNat m` and the negative case `Int.negSucc m`.
    match n with
    | Int.ofNat m =>
      -- Induct upward on `m`, using `key1` to step from `p m` to `p (m + 1)`.
      induction m with
      | zero => simpa
      | succ d hd =>
        rw [show (Int.ofNat (d + 1) : ℤ) = (Int.ofNat d : ℤ) + 1 by simp]
        rw [← key1]
        exact hd
    | Int.negSucc m =>
      -- Induct downward on `m`, using `key1` to step from `p (-(d+1))` to `p (-(d+2))`.
      induction m with
      | zero => rw [key1]; simpa
      | succ d hd =>
        have heq : Int.negSucc (d + 1) + 1 = Int.negSucc d := by
          simp [Int.negSucc_eq]
        rw [key1, heq]
        exact hd

end two_sided_induction

section gauss_formula

-- by landing in ℕ recursion (rather than subtraction), we avoid the perils
-- of nat subtraction
def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => n + 1 + f n

example : f 1 = 1 := by
  -- `f` unfolds and computes directly.
  decide

example (n : ℕ) : 2 * f n = n * (n + 1) := by
  induction n with
  | zero =>
    -- `f 0 = 0`, and `2 * 0 = 0 * 1`.
    unfold f; simp
  | succ d hd =>
    -- `f (d + 1) = (d + 1) + f d`; substitute and use the induction hypothesis `hd`.
    unfold f
    linarith

end gauss_formula

section telescoping_sum

variable {R : Type*} [CommRing R]

example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  -- Distribute `(1 - a)` over the sum...
  rw [Finset.mul_sum]
  -- ...then this is exactly the mathlib telescoping-sum induction principle.
  exact Finset.sum_range_induction (fun k => (1 - a) * a ^ k) (fun n => 1 - a ^ n)
    (by simp) n (fun k _ => by ring)

-- doing your induction "by hand"
example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  induction n with
  | zero =>
    -- Both sides are `0`.
    simp
  | succ d hd =>
    -- Peel off the last term of the sum, then apply the induction hypothesis `hd` and simplify.
    rw [Finset.sum_range_succ, mul_add, hd]
    ring

end telescoping_sum

section triple_negation

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

end triple_negation

section prime_two_or_odd

example (p : ℕ) : p.Prime → p = 2 ∨ p % 2 = 1 := by
  -- This is exactly the mathlib lemma `Nat.Prime.eq_two_or_odd`.
  exact fun a => a.eq_two_or_odd

end prime_two_or_odd

section three_fac_of_sum_consecutive_primes

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
  have hab : a < a * b := by omega
  -- From `a < a * b`, `b` must be greater than `1`.
  have hb2 : 1 < b := one_lt_of_nontrivial_factor hab
  -- And `b < k`, since `b < a * b = k` (as `a ≥ 2`).
  have hbk : b < k := by
    have h2b : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
    omega
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
  -- `k` lies strictly between `p` and `q`, so it can't be prime.
  have hk' : ¬ k.Prime := consecutive k (by omega) (by omega)
  have h2k : 2 ≤ k := by have := hp.two_le; omega
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

end three_fac_of_sum_consecutive_primes

section frog_problem

@[ext]
structure Frog where
  -- A frog hangs out on the natural number line of lily pads
  location : ℕ → ℕ
  -- At time 0, it sits on location 0
  location_zero : location 0 = 0
  -- For some fixed step size,
  step_size : ℕ
  -- the frog jumps `step_size` units to the right each second.
  step : ∀ n, location (n + 1) = location n + step_size

lemma frog_explicit_formula (f : Frog) :
    -- Show that the position of the frog at time n is n * step_size.
    ∀ n, f.location n = n * f.step_size := by
  intro n
  induction n with
  | zero =>
    -- At time `0` the frog is at `0`, and `0 = 0 * step_size`.
    rw [f.location_zero]; norm_num
  | succ d hd =>
    -- `f.location (d + 1) = f.location d + step_size`; substitute the induction hypothesis `hd`.
    rw [f.step, hd]; ring

-- We can define a frog just by giving its step size
def frogOfStepSize (step_size : ℕ) : Frog where
  location := fun n => n * step_size
  location_zero := by simp
  step_size := step_size
  step := by intro n; ring

-- and every frog can be defined in this way
lemma frog_eq_frog_of_step_size (f : Frog) :
    f = frogOfStepSize f.step_size := by
  -- Two frogs are equal iff they agree at every time `n` (and have the same step size).
  ext n
  · -- Positions agree, by the explicit formula proved above.
    rw [frog_explicit_formula]; simp [frogOfStepSize]
  · -- Step sizes agree trivially, by definition of `frogOfStepSize`.
    simp [frogOfStepSize]

lemma catch_the_frog :
    -- Show that there is a way to check one lily pad each second
    ∃ (strategy : ℕ → ℕ),
    -- so that no matter how fast the frog travels,
    ∀ step_size,
    -- you'll eventually catch it.
    ∃ catch_time > 0,
    strategy catch_time = (frogOfStepSize step_size).location catch_time := by
  -- Strategy: at time `n`, check lily pad `n * (n - 1)`.
  use fun n => n * (n - 1)
  -- Fix an arbitrary step size `k`.
  intro k
  -- We claim the frog is caught at time `k + 1`.
  use k + 1
  constructor
  · -- `k + 1 > 0` trivially.
    exact Nat.succ_pos k
  · -- At time `k + 1`, both the strategy and the frog are at `k * (k + 1)`.
    simp [frogOfStepSize]

end frog_problem

end AdditionalProblems
