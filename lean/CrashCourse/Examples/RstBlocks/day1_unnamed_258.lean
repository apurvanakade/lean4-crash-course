-- --------------------------------------------------------------------------
--
-- You can prove exactly one of the following three using just
-- ``exact``, ``intro``, ``have``, and ``apply``.
--
-- Can you find which one?
--
-- --------------------------------------------------------------------------

theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P := by
  sorry

theorem contrapositive_converse (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  sorry

example (P : Prop) : ¬ P → ¬ ¬ ¬ P := by
  sorry