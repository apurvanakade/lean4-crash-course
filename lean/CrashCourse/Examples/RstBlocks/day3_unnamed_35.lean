import Mathlib.Tactic

-- --------------------------------------------------------------------------
--
--   ``rw``
--
--     If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then
--     ``rw [f]`` replaces ``P`` with ``Q`` in the target.
--     Other variants:
--       ``rw [f] at hp``, ``rw [← f]``, ``rw [← f] at hr``.
--
--   Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

theorem add_self_self_eq_double
    (x : ℕ) :
    x + x = 2 * x := by
  ring

-- For the following problem, use
--   mul_comm a b : a * b = b * a

example (a b c d : ℕ)
    (hyp : c = d * a + b)
    (hyp' : b = a * d) :
    c = 2 * (a * d) := by
  sorry

-- For the following problem, use
--   Nat.sub_self (x : ℕ) : x - x = 0

example (a b c d : ℕ)
    (hyp : c = b * a - d)
    (hyp' : d = a * b) :
    c = 0 := by
  sorry