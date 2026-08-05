-- --------------------------------------------------------------------------
--
-- Recall that
--   ``¬ P`` is ``P → False``,
--   ``¬ (¬ P)`` is ``(P → False) → False``, and so on.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

theorem self_imp_not_not_self (P : Prop) : P → ¬ (¬ P) := by
  sorry

theorem contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  sorry

example (P : Prop) : ¬ (¬ (¬ P)) → ¬ P := by
  sorry