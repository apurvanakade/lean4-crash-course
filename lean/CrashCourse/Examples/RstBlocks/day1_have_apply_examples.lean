-- --------------------------------------------------------------------------
--
-- ``have``
--
--   If ``f`` is a term of type ``P → Q`` and
--   ``hp`` is a term of type ``P``, then
--   ``have hq := f hp`` creates the hypothesis ``hq : Q`` .
--
--
-- ``apply``
--
--   If the target of the current goal is ``Q`` and
--   ``f`` is a term of type ``P → Q``, then
--   ``apply f`` changes target to ``P``.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R := by
  sorry

example (P Q R S T U : Type)
    (hpq : P → Q)
    (hqr : Q → R)
    (hqt : Q → T)
    (hst : S → T)
    (htu : T → U) :
    P → U := by
  sorry