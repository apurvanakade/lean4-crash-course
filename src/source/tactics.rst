.. _tactics:

*********************
Glossary of tactics
*********************

Implications in Lean
======================

.. list-table::
   :widths: 20 80
   :header-rows: 0

   * - ``exact``
     - If
       ``P`` is the target of the current goal
       and ``hp`` is a term of type ``P``,
       then ``exact hp`` will close the goal.

       Mathematically, this saying "this is *exactly* what we were required to prove".

   * - ``intro``
     - If the target of the current goal is a function ``P → Q``,
       then ``intro hp`` will produce a hypothesis
       ``hp : P`` and change the target to  ``Q``.

       Mathematically, this is saying that in order to define a function from ``P`` to ``Q``,
       we first need to choose an arbitrary element of ``P``.

.. list-table::
   :widths: 20 80
   :header-rows: 0

   * - ``have``
     - ``have`` is used to create intermediate variables.

       If ``f`` is a term of type ``P → Q`` and
       ``hp`` is a term of type ``P``, then
       ``have hq := f hp`` creates the hypothesis ``hq : Q`` .

   * - ``apply``
     - ``apply`` is used for backward reasoning.

       If the target of the current goal is ``Q`` and
       ``f`` is a term of type ``P → Q``, then
       ``apply f`` changes target to ``P``.

       Mathematically, this is equivalent to saying "because ``P`` implies ``Q``, to prove ``Q`` it suffices to prove ``P``".

Proof by contradiction
========================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``exfalso``
    - Changes the target of the current goal to ``False``.

      The name derives from `"ex falso, quodlibet" <https://en.wikipedia.org/wiki/Principle_of_explosion>`__ which translates to "from contradiction, anything".
      You should use this tactic when there are contradictory hypotheses present.

  * - ``by_cases``
    - If ``P : Prop``, then ``by_cases P`` creates two goals,
      the first with a hypothesis ``hp : P`` and second with a hypothesis ``hp : ¬ P``.

      Mathematically, this is saying either ``P`` is true or ``P`` is false.
      ``by_cases`` is the most direct application of the law of excluded middle.

  * - ``by_contra``
    - If the target of the current goal is  ``Q``,
      then ``by_contra`` changes the target to  ``False`` and
      adds ``hnq : ¬ Q`` as a hypothesis.

      Mathematically, this is proof by contradiction.

  * - ``push Not``
    - ``push Not`` simplifies negations in the target.

      For example, if the target of the current goal is ``¬ ¬ P``, then
      ``push Not`` simplifies it to ``P``.

      You can also push negations across a hypothesis ``hp : P`` using ``push Not at hp``.

  * - ``contrapose!``
    - If the target of the current goal is  ``P → Q``,
      then ``contrapose!`` changes the target to  ``¬ Q → ¬ P``.

      If the target of the current goal is ``Q``
      and one of the hypotheses is ``hp : P``,
      then ``contrapose! hp`` changes the target to  ``¬ P``
      and changes the hypothesis to ``hp : ¬ Q``.

      Mathematically, this is replacing the target by its contrapositive.


And / Or
===================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``obtain``
    - ``obtain`` is a general tactic that breaks a complicated term into simpler ones.

      If ``hpq`` is a term of type ``P ∧ Q``, then
      ``obtain ⟨hp, hq⟩ := hpq`` breaks it into ``hp : P`` and ``hq : Q``.

      If ``fg`` is a term of type ``P ↔ Q``, then
      ``obtain ⟨f, g⟩ := fg`` breaks it into ``f : P → Q`` and ``g : Q → P``.

      If ``hpq`` is a term of type ``P ∨ Q``, then
      ``obtain hp | hq := hpq`` creates two goals and adds the hypothesis ``hp : P`` in one and ``hq : Q`` in the other.

  * - ``constructor``
    - ``constructor`` is a general tactic that breaks a complicated goal into simpler ones.

      If the target of the current goal is ``P ∧ Q``, then
      ``constructor`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P × Q``, then
      ``constructor`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P ↔ Q``, then
      ``constructor`` breaks up the goal into two goals with targets ``P → Q`` and ``Q → P``.

  * - ``left``
    - If the target of the current goal is ``P ∨ Q``, then
      ``left`` changes the target to ``P``.

  * - ``right``
    - If the target of the current goal is ``P ∨ Q``, then
      ``right`` changes the target to ``Q``.

Quantifiers
==============

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - If ``hp`` is a term of type ``∀ x : X, P x`` and
      ``y`` is a term of type ``X`` then
      ``have hpy := hp y`` creates a hypothesis ``hpy : P y``.

  * - ``intro``
    - If the target of the current goal is ``∀ x : X, P x``, then
      ``intro x`` creates a hypothesis ``x : X`` and
      changes the target to ``P x``.

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``obtain``
    - If ``hp`` is a term of type ``∃ x : X, P x``, then
      ``obtain ⟨x, key⟩ := hp`` breaks it into
      ``x : X`` and ``key : P x``.

  * - ``use``
    - If the target of the current goal is ``∃ x : X, P x``
      and ``y`` is a term of type ``X``, then
      ``use y`` changes the target to ``P y`` and tries to close the goal.

Proving "trivial" statements
=============================

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``norm_num``
    - ``norm_num`` is Lean’s calculator. If the target has a proof that involves *only* numbers and arithmetic operations,
      then ``norm_num`` will close this goal.

      If ``hp : P`` is an assumption then ``norm_num at hp`` tries to simplify ``hp`` using basic arithmetic operations.

  * - ``ring``
    - ``ring`` is Lean's symbolic manipulator.
      If the target has a proof that involves *only* algebraic operations,
      then ``ring`` will close the goal.

      If ``hp : P`` is an assumption then ``ring at hp`` tries to simplify ``hp`` using basic algebraic operations.

  * - ``linarith``
    - ``linarith`` is Lean's inequality solver.

  * - ``simp``
    - ``simp`` is a very complex tactic that tries to use theorems from the mathlib library to close the goal.
      You should only ever use ``simp`` to *close a goal* because its behavior changes as more theorems get added to the library.


Equality
===========

.. list-table::
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then

        ``rw [f]`` searches for ``P`` in the target and replaces it with ``Q``.

        ``rw [← f]`` searches for ``Q`` in the target and replaces it with ``P``.

      If additionally, ``hr : R`` is a hypothesis, then

        ``rw [f] at hr`` searches for ``P`` in the expression ``R`` and replaces it with ``Q``.

        ``rw [← f] at hr`` searches for ``Q`` in the expression ``R`` and replaces it with ``P``.

      Mathematically, this is saying because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around).

  * - ``norm_cast``
    - ``norm_cast`` tries to clear out coercions between types (e.g. ``ℕ → ℤ`` or ``ℕ → ℚ``).

      ``norm_cast at hp`` tries to clear out coercions in the hypothesis ``hp``.
