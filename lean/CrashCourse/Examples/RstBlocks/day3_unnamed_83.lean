import Mathlib.Tactic
open Function

-- --------------------------------------------------------------------------
--
-- ``unfold``
--
--   If it gets hard to keep track of the definition of ``Surjective``,
--   you can use ``unfold Function.Surjective`` or ``unfold Function.Surjective at h``
--   to get rid of it.
--
-- Delete the ``sorry`` below and replace them with a legitimate proof.
--
-- --------------------------------------------------------------------------

variable (X Y Z : Type)
variable (f : X → Y) (g : Y → Z)

-- Surjective (f : X → Y) := ∀ y, ∃ x, f x = y

example
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

example
    (hgf : Surjective (g ∘ f)) :
    Surjective g := by
  sorry