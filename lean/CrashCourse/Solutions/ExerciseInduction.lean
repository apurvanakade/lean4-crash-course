import Mathlib.Tactic

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
    ring_nf
    ring_nf at hd
    omega

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
