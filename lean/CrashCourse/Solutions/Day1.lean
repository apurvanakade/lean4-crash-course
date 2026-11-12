import Mathlib.Tactic

namespace Day1

example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R := by
  -- `f` turns `hp : P` into a proof of `Q`...
  have hq := f hp
  -- ...and `g` turns that into a proof of `R`.
  have hr := g hq
  exact hr

example (P Q R S T U : Prop)
    (hpq : P → Q)
    (hqr : Q → R)
    (hqt : Q → T)
    (hst : S → T)
    (htu : T → U) :
    P → U := by
  intro hp
  -- Chain `P → Q → T → U`; `hqr` and `hst` are not needed.
  have hq := hpq hp
  have ht := hqt hq
  exact htu ht

theorem tautology (P : Prop) (hp : P) : P := by
  exact hp

theorem tautology' (P : Prop) : P → P := by
  intro hp
  exact hp

example (P Q : Prop) : (P → (Q → P)) := by
  intro hp _
  exact hp

-- First way: the goal is literally the hypothesis.
example (P Q : Prop) : ((Q → P) → (Q → P)) := by
  intro h
  exact h

-- Second way: introduce `hq` too and apply `h` to it.
example (P Q : Prop) : ((Q → P) → (Q → P)) := by
  intro h hq
  exact h hq

theorem self_imp_not_not_self (P : Prop) : P → ¬ (¬ P) := by
  -- `¬ ¬ P` is `(P → False) → False`, so introduce `hnp : P → False`.
  intro hp hnp
  exact hnp hp

theorem contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

example (P : Prop) : ¬ (¬ (¬ P)) → ¬ P := by
  intro hnnnp hp
  -- It suffices to prove `¬ ¬ P`; introduce `hnp : ¬ P`...
  apply hnnnp
  intro hnp
  -- ...which contradicts `hp : P`.
  exact hnp hp

-- Of the next three, only `¬ P → ¬ ¬ ¬ P` can be proved with just
-- `exact`, `intro`, `have` and `apply`.
example (P : Prop) : ¬ P → ¬ ¬ ¬ P := by
  intro hnp hnnp
  exact hnnp hnp

theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P := by
  intro hnnp
  -- Assume `¬ P` for contradiction; it contradicts `hnnp`.
  by_contra hnp
  exact hnnp hnp

theorem contrapositive_converse (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  -- `contrapose!` turns the goal `P → Q` into `¬ Q → ¬ P`.
  contrapose!
  exact h

theorem principle_of_explosion (P Q : Prop) : P → (¬ P → Q) := by
  intro hp hnp
  -- Reduce to proving `False`, which `hnp hp` provides.
  exfalso
  exact hnp hp

end Day1
