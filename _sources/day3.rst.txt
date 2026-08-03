.. _day3:

***********************
Infinitely Many Primes
***********************

Today we will prove that there are infinitely many primes using `mathlib library <https://leanprover-community.github.io/mathlib4_docs/>`__. Our focus will be on how to *use* the library to prove more complicated theorems. Remember to always **save your work**.

Equality 
===========
So far we have not seen how to deal with propositions of the form ``P = Q``, for example, ``1 + 2 + ... + n = n(n + 1)/2``. Proving these propositions by hand requires messing around with the axioms of type theory.
The standard trick is to make the LHS (almost) equal or to the RHS and then use one of the simplifiers (``norm_num``, ``ring``, ``linarith``, or ``simp``) to close the goal. *Using* equalities on the other hand is very easy. The rewrite tactic (usually shortened to ``rw``) lets you replace the left hand side of an equality with the right hand side.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then

        ``rw [f]`` searches for ``P`` in the target and replaces it with ``Q``.

        ``rw [← f]`` searches for ``Q`` in the target and replaces it with ``P``.

      Additionally, if ``hr : R`` is a hypothesis, then

        ``rw [f] at hr`` searches for ``P`` in the expression ``R`` and replaces it with ``Q``.

        ``rw [← f] at hr`` searches for ``Q`` in the expression ``R`` and replaces it with ``P``.

      Mathematically, this is saying "because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around)".

To get the left arrow, type ``\l`` followed by tab.

.. code:: lean4

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


Surjective functions
----------------------
Recall that a function ``f : X → Y`` is surjective if for every ``y : Y`` there exists a term ``x : X``
such that ``f(x) = y``. 
In type theory, for every function ``f`` we can define a corresponding proposition 
``surjective (f) := ∀ y, ∃ x, f x = y`` and a function being surjective is equivalent to saying that the proposition ``surjective(f)`` is inhabited.

.. code:: lean4

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


Creating subgoals
===================
Often when we write a long proof in math, we break it up into simpler problems.
This is done in Lean using the ``have`` tactic. 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - ``have hp : P`` creates a new goal with target ``P`` and
      adds ``hp : P`` as a hypothesis to the original goal.

The use of ``have`` that we have already seen is related to this one.
When you use the tactic ``have hq := f hp``
Lean is internally replacing it with ``have hq : Q := f hp``.

``have`` is crucial for being able to use theorems from the library.
To use these theorems you have to create terms that match the hypothesis *exactly*.
Consider the following example.
The type ``n > 0`` is not the same as ``0 < n``.
If you need a term of type ``n > 0`` and you only have ``hn : 0 < n``, then you can use
``have hn2 : n > 0 := by linarith`` and you will have constructed a term ``hn2`` of type ``n > 0``.


We will need the following lemma later. Remember to save your proof.
(Here's a :doc:`hint <../hint_1_have_exercise>` if you need one.)
**Warning:** If you need to type the divisibility symbol, type ``\mid``.
This is **not** the vertical line on your keyboard.

.. code:: lean4

  import Mathlib.Tactic

  -- --------------------------------------------------------------------------
  --
  -- ``have``
  --
  --   ``have hp : P`` creates a new goal with target ``P`` and
  --   adds ``hp : P`` as a hypothesis to the original goal.
  --
  -- You'll need the following theorem from the library:
  --
  -- Nat.dvd_sub' : k ∣ m → k ∣ n → k ∣ m - n
  --
  --    (Note that you don't need to provide m n k as inputs to dvd_sub'.
  --    Lean can infer these from the rest of the expression.
  --    More on this tomorrow.)
  --
  -- Delete the ``sorry`` below and replace it with a legitimate proof.
  --
  -- --------------------------------------------------------------------------

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) := by
    sorry


Infinitely many primes 
=======================

We'll now prove that there are infinitely many primes. 
The strategy is to show that there is a prime greater than ``n``, for every natural number ``n``.
We will choose this prime to be smallest non-trivial factor of ``n! + 1``. 
We'll need the following definitions and theorems from the library.

**Primes**
  * ``m ∣ n := ∃ k : ℕ, n = m * k``
  * ``p.Prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)``
  * ``Nat.Prime.one_lt : p.Prime → 1 < p``

**Factorials**
  * ``n ! := Nat.factorial n``
  * ``Nat.factorial_pos : ∀ (n : ℕ), 0 < n !``
  * ``Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !``

**Smallest factor**
  * ``Nat.minFac n :=`` smallest non-trivial factor of ``n``
  * ``Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime``
  * ``Nat.minFac_pos : ∀ (n : ℕ), 0 < Nat.minFac n``
  * ``Nat.minFac_dvd : ∀ (n : ℕ), Nat.minFac n ∣ n``

Check out `Mathlib.Data.Nat.Prime.Basic <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Basic.html>`__ for more theorems about primes.
The exercise below is very open-ended.
You should take your time, check the goal window at every step, and sketch out the proof on paper whenever you get lost.

.. code:: lean4

  import Mathlib.Tactic

  -- Lean 4 / mathlib4 uses classical logic (the law of excluded middle) by
  -- default, so no extra imports or options are needed to use it.

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) := by
    sorry

  -- dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1)
  --
  -- m ∣ n := ∃ k : ℕ, n = m * k
  -- p.Prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)
  -- Nat.Prime.one_lt : p.Prime → 1 < p
  --
  -- n ! := Nat.factorial n
  -- Nat.factorial_pos : ∀ (n : ℕ), 0 < n !
  -- Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !
  --
  -- Nat.minFac n := smallest non-trivial factor of n
  -- Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime
  -- Nat.minFac_pos : ∀ (n : ℕ), 0 < Nat.minFac n
  -- Nat.minFac_dvd : ∀ (n : ℕ), Nat.minFac n ∣ n

  theorem exists_infinite_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p ≥ n := by
    set p := (Nat.factorial n + 1).minFac
    sorry


Final remarks 
=================
It would be great if there was a one-to-one correspondence between "hand-written proofs" and proofs in Lean. But that is far from the case. When we write proofs we leave out a lot of details without even realizing it and expect the reader to be intelligent enough to fill them in. This is both a bug and feature. On the one hand this makes proofs readable. On the other hand too many "obviously true" arguments make proofs undecipherable and often wrong.

Unlike human readers, computers are pretty dumb (as of writing these notes). They can only do what you tell them to do and you cannot expect them to "fill in the details". But it is humanly impossible to teach a computer every single trivial fact about, say the natural numbers. The `Lean math library <https://leanprover-community.github.io/mathlib4_docs/>`__ contains a lot of trivial theorems but this collection is far from comprehensive.
So theorem proving in Lean often involves the following steps:

* Scan the library to see which definitions and theorems might be useful.

* Choose the right hypotheses and wording for your theorem to match the theorems in the library. (Sadly, changing the wording slightly might end up making the proof infinitely harder to prove.)

* Break the theorem into small lemmas so that you can use the simplifiers more frequently.

The hope is that one day we won’t have to do this and a theorem proving AI will eliminate the difference between human proofs and machine proofs.