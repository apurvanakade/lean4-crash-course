.. _introduction:

*****************
Introduction
*****************

What is Lean?
===============
`Lean <https://lean-lang.org/>`__ is an open source proof-checker and a proof-assistant. 
One can *explain* mathematical proofs to it and it can check their correctness.
It also simplifies the proof writing process by providing ``goals`` and ``tactics``.

Lean is built on top of a formal system called type theory.
In type theory, the basic notions are "terms" and "types" --- compare to "elements" and "sets" in set theory.
Every term has a type, and types are just a special kind of term.
Terms can be interpreted as mathematical objects, functions, propositions, or proofs.
The only two things Lean can do are *create* terms and *check* their types.
By iterating these two operations, we can teach Lean to verify complex mathematical proofs.

.. code-block:: lean4

  import Mathlib.Tactic

  def x := 2 + 2                                  -- a natural number
  def f (x : ℕ) := x + 3                          -- a function
  def easy_theorem_statement := 2 + 2 = 4         -- a proposition
  def fermats_last_theorem_statement              -- another proposition
      :=
    ∀ n : ℕ, n > 2 →
    ¬ (∃ x y z : ℕ, (x ^ n + y ^ n = z ^ n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0))

  theorem easy_proof : easy_theorem_statement := by  -- proof of easy_theorem
    rfl

  theorem hard_proof : fermats_last_theorem_statement := by  -- cheating!
    sorry

  #check x
  #check f
  #check easy_theorem_statement
  #check fermats_last_theorem_statement
  #check easy_proof
  #check hard_proof


How to use these notes
=========================
Every once in a while, you will see a code snippet like this:

.. code-block:: lean4

    #eval "Hello, World!"

Clicking on the ``try it!`` button in the upper right corner will
open a copy in a window
so that you can edit it,
and Lean provides feedback in the ``Lean Infoview`` window.
We use this feature to provide exercises inline in the notes. 
We recommend attempting each exercise as you go along.

These notes are designed for a 5-day Lean crash course at Mathcamp 2020.
On Days 1 and 2 you'll learn the basics of type theory and some basic ``tactics`` in Lean. 
On Days 3, 4, 5 you'll use these to prove increasingly complex theorems, namely the infinitude of primes and irrationality of :math:`\sqrt{2}`.

These notes provide a sneak-peek into the world of theorem proving in Lean and are by no means comprehensive.
It is recommended that you simultaneously attempt at least one of the following two options.

#. Play the `Natural Number Game`_.
#. Read `Theorem Proving in Lean 4`_.

The `Natural Number Game`_ is a fun (and highly addictive!) game that proves some basic properties of natural numbers in Lean.
`Theorem Proving in Lean 4`_ is a comprehensive online book that aims to cover all the theorem proving aspects of Lean in great detail. 

The Lean community is very welcoming to newcomers, and people are available on the `Lean Zulip chat group`_ round the clock
to answer questions. 
You're highly encouraged to join it.


Acknowledgments
===================
These notes are developed by `Apurva Nakade <https://apurvanakade.github.io>`__ and `Jalex Stark <https://jalexstark.com/>`__ 
with a lot of help from Mathcamp campers and Mathcamp staff Joanna and Maya (thanks!).
Large chunks of these notes are taken from various learning resources available on the `leanprover-community website <https://leanprover-community.github.io/learn.html>`__.


Useful Links
==================
For an up-to-date list of Lean resources, see `All things Lean <https://apurvanakade.github.io/blog/all-things-lean.html>`__.


.. _`Natural Number Game`: https://adam.math.hhu.de/#/g/leanprover-community/NNG4
.. _`Theorem Proving in Lean 4`: https://leanprover.github.io/theorem_proving_in_lean4/
.. _`Lean Zulip chat group`: https://leanprover.zulipchat.com/
