import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

#print Group

class CyclicGroup (G : Type*) extends Group G where
  has_generator : ∃ g : G, ∀ x : G, ∃ n : ℤ, x = g ^ n

-- zpow_add : ∀ {G : Type u_1} [inst : Group G] (a : G) (m n : ℤ), a ^ (m + n) = a ^ m * a ^ n

lemma mul_comm_of_cyclic
    {G : Type*}
    [hc : CyclicGroup G]
    (g : G) :
    ∀ a b : G, a * b = b * a := by
  have has_generator := hc.has_generator
  sorry