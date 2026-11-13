.. _tactics_extra:

*************
More tactics
*************

These tactics are not needed for the exercises in the course,
but you will see them all the time in mathlib and in other people's Lean code.
(The tactics needed for the exercises are in the :doc:`Glossary of tactics<tactics>`.)

Introducing and breaking up hypotheses
========================================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - `rintro <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rintro>`__
    - ``rintro`` is ``intro`` followed by ``obtain``:
      it introduces a hypothesis and breaks it up in one step.

      If the target is ``P ∧ Q → R``, then
      ``rintro ⟨hp, hq⟩`` introduces ``hp : P`` and ``hq : Q``.

      If the target is ``P ∨ Q → R``, then
      ``rintro (hp | hq)`` creates two goals, one with ``hp : P`` and one with ``hq : Q``.

      If the target is ``(∃ x : X, P x) → R``, then
      ``rintro ⟨x, hx⟩`` introduces ``x : X`` and ``hx : P x``.

  * - `rcases <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rcases>`__
    - ``rcases`` is the tactic ``obtain`` is built on: ``rcases hpq with ⟨hp, hq⟩`` does the same as
      ``obtain ⟨hp, hq⟩ := hpq``.

  * - `cases <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#cases>`__
    - ``cases`` breaks up a hypothesis like ``obtain``, but names the cases explicitly.

      If ``hpq : P ∨ Q`` then

      .. code-block:: lean

        cases hpq with
        | inl hp => ...
        | inr hq => ...

      creates the two goals with ``hp : P`` and ``hq : Q``.

  * - `induction' <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Cases.html>`__
    - ``induction' n with k ih`` is a shorter way to do induction on ``n : ℕ``:
      it produces the base case, and the inductive step with ``ih`` the statement for ``k``
      and the target the statement for ``k + 1``.
      (``induction n with | zero => ... | succ k ih => ...`` does the same.)

  * - `specialize <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#specialize>`__
    - If ``hp`` is a term of type ``∀ x : X, P x`` and ``y : X``, then
      ``specialize hp y`` *replaces* ``hp`` by ``hp : P y``.
      (Compare ``have hpy := hp y``, which keeps ``hp``.)

  * - `refine <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#refine>`__
    - ``refine`` is like ``exact`` but lets you leave holes ``?_`` in the term.
      Each hole becomes a new goal.

      For example, ``refine ⟨?_, ?_⟩`` splits a goal ``P ∧ Q`` into two goals,
      and ``refine ⟨y, ?_⟩`` turns the goal ``∃ x, P x`` into ``P y``.

Writing proofs on paper
=========================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - `calc <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#calc>`__
    - ``calc`` lets you write a chain of equalities or inequalities,
      with a justification for each step.

      .. code-block:: lean

        calc a = b := by rw [h1]
          _ = c := by ring
          _ ≤ d := h2

      This proves ``a ≤ d``.
      Mathematically, this is exactly how you would write the chain on paper.

  * - `by_contra! <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ByContra.html>`__
    - ``by_contra!`` is ``by_contra`` followed by pushing the negation through the new hypothesis.

      If the target is ``∀ x, P x``, then ``by_contra! h`` gives ``h : ∃ x, ¬ P x``
      (rather than ``h : ¬ ∀ x, P x``).

Closing goals
===============

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - `simpa <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#simpa>`__
    - ``simpa using h`` simplifies both the target and the term ``h``
      and then closes the goal if the results match.
      It is the safe way to use ``simp`` on a goal you have not yet fully reduced.

  * - `aesop <https://leanprover-community.github.io/mathlib4_docs/Aesop/Frontend/Tactic.html>`__
    - A general-purpose proof search tool.
      It combines ``simp``, ``intro``, ``constructor``, ``obtain`` and more,
      and is often able to close goals that only need a few routine steps.

  * - `tauto <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Tauto.html>`__
    - Closes goals that follow from propositional logic alone
      (``∧``, ``∨``, ``¬``, ``→``, ``↔``).

  * - `split_ifs <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SplitIfs.html>`__
    - Splits every ``if ... then ... else ...`` in the target into cases,
      adding the condition (or its negation) as a hypothesis.

Rewriting and comparing parts
===============================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - `simp_rw <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SimpRw.html>`__
    - Like ``rw``, but repeats and also works under binders such as ``∀ x, ...`` and ``∃ x, ...``.
      ``rw`` fails there.

  * - `ext <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#ext>`__
    - To prove two functions or sets are equal, ``ext x`` reduces to showing they agree on an arbitrary ``x``.
      For sets, the goal ``s = t`` becomes ``x ∈ s ↔ x ∈ t``.

  * - `funext <https://leanprover-community.github.io/mathlib4_docs/Init/NotationExtra.html>`__
    - To prove two functions are equal, ``funext x`` reduces to showing
      ``f x = g x`` for an arbitrary ``x``.

  * - `apply_fun <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ApplyFun.html>`__
    - If ``h : a = b`` then ``apply_fun f at h`` changes ``h`` to ``h : f a = f b``.
      ``apply_fun f`` on the goal ``a = b`` changes it to ``f a = f b``
      (you will then need to know ``f`` is injective).

  * - `convert <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Convert.html>`__
    - ``convert h`` closes the goal using ``h`` when the type of ``h`` is *almost* the target:
      it leaves a new goal for each place where they differ.
      ``convert h using 2`` limits how deep it looks for differences.

  * - `congr <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#congr>`__
    - If the goal is ``f a = f b``, then ``congr`` reduces it to ``a = b``.
      More generally, it compares the two sides piece by piece
      and leaves a goal for each place where they differ.

  * - `gcongr <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr/Core.html>`__
    - The same idea for inequalities:
      if the goal is ``a + c ≤ b + c``, or ``x * a ≤ x * b`` with ``0 ≤ x``,
      then ``gcongr`` reduces it to ``a ≤ b``.
      Side goals such as ``0 ≤ x`` are tried with ``positivity``.

Finding lemmas
================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - `exact? <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#exact___>`__
    - Searches mathlib for a lemma that closes the goal and tells you what it found.

  * - `apply? <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#apply___>`__
    - Same, but also suggests lemmas that only make progress on the goal.

  * - `rw? <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rw___>`__
    - Suggests rewrites that apply to the current goal.
