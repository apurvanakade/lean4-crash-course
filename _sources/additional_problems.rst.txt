.. _additional_problems:

********************************
Additional Problems for Practice
********************************

The five days above are the whole course, but here are a few extra problems that never made it into
the schedule. They're independent of each other and of the daily material, so pick whichever looks fun.
Full worked solutions are linked in the sidebar under "Solutions on GitHub".

Induction & recursion practice
================================

A rewriting puzzle
--------------------
Let :math:`p : \mathbb{N} \to \mathrm{Prop}`, and suppose :math:`p(n)` holds for some fixed :math:`n`.
Suppose further that :math:`p(m) \iff p(m+8)` and :math:`p(m+3) \iff p(m)` for every :math:`m \in \mathbb{N}`.
Show that :math:`p(n+1)` holds.

.. code-block:: lean4
  :name: rw_puzzle

  import Mathlib.Tactic

  example
      (p : ℕ → Prop) (n : ℕ) (hn : p n)
      (h8 : ∀ n, p n ↔ p (n + 8))
      (h3 : ∀ n, p (n + 3) ↔ p n) :
      p (n + 1) := by
    sorry

Two small types
-----------------
Show that the type with no elements is not the type with one element, i.e. :math:`\mathrm{Fin}\,0 \ne \mathrm{Fin}\,1`.

.. code-block:: lean4
  :name: fin_zero_ne_one

  import Mathlib.Tactic

  example : Fin 0 ≠ Fin 1 := by
    sorry

Reflexivity from symmetry and transitivity
---------------------------------------------
Let :math:`r` be a relation on :math:`\mathbb{N}` that is symmetric and transitive, and suppose every
:math:`x \in \mathbb{N}` is :math:`r`-related to *some* :math:`y` (i.e. :math:`r` is *serial*).
Show that :math:`r` must in fact be reflexive.

.. code-block:: lean4
  :name: reflexive_of_symmetric_and_transitive

  import Mathlib.Tactic

  theorem reflexive_of_symmetric_and_transitive (r : ℕ → ℕ → Prop)
      (h_symm : Std.Symm r) (h_trans : IsTrans ℕ r)
      (h_connected : ∀ x, ∃ y, r x y) :
      Std.Refl r where
    refl x := by
      sorry

Every number is even or odd
-----------------------------
Show that every :math:`n \in \mathbb{N}` can be written as :math:`2k` or :math:`2k+1` for some :math:`k`.

.. code-block:: lean4
  :name: even_or_odd

  import Mathlib.Tactic

  lemma even_or_odd (n : ℕ) :
      (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
    sorry

Induction in both directions
-------------------------------
Let :math:`p : \mathbb{Z} \to \mathrm{Prop}` satisfy :math:`p(n) \Rightarrow p(n+1)` and
:math:`p(n) \Rightarrow p(n-1)` for every :math:`n \in \mathbb{Z}`.
Show that :math:`p` holds everywhere on :math:`\mathbb{Z}` if and only if it holds at :math:`0`.
(Ordinary induction on :math:`\mathbb{N}` only walks in one direction --- here you have to walk outward
from :math:`0` in both directions.)

.. code-block:: lean4
  :name: two_sided_induction

  import Mathlib.Tactic

  example
      (p : ℤ → Prop)
      (p_succ : ∀ n, p n → p (n + 1))
      (p_pred : ∀ n, p n → p (n - 1)) :
      (∀ n, p n) ↔ p 0 := by
    sorry

Gauss's formula
------------------
Define :math:`f : \mathbb{N} \to \mathbb{N}` recursively by :math:`f(0) = 0` and :math:`f(n+1) = (n+1) + f(n)`,
so that :math:`f(n) = 0 + 1 + \cdots + n`. Show :math:`f(1) = 1` and, more generally,
:math:`2f(n) = n(n+1)` for every :math:`n`.

.. code-block:: lean4
  :name: gauss_formula

  import Mathlib.Tactic

  -- landing in ℕ recursion (rather than subtraction) avoids the perils of nat subtraction
  def f : ℕ → ℕ
    | 0 => 0
    | (n + 1) => n + 1 + f n

  example : f 1 = 1 := by
    sorry

  example (n : ℕ) : 2 * f n = n * (n + 1) := by
    sorry

Telescoping sums
-------------------
Let :math:`R` be a commutative ring, :math:`a \in R`, and :math:`n \in \mathbb{N}`. Show

.. math::

  (1 - a) \sum_{k=0}^{n-1} a^k = 1 - a^n.

Prove it twice: once by finding the matching lemma already in mathlib, and once "by hand" by induction on :math:`n`.

.. code-block:: lean4
  :name: telescoping_sum

  import Mathlib.Tactic

  variable {R : Type*} [CommRing R]

  -- find the matching lemma in mathlib
  example (n : ℕ) (a : R) :
      (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
    sorry

  -- now redo it "by hand", by induction on n
  example (n : ℕ) (a : R) :
      (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
    sorry

Primes & parity practice
==========================

Triple negation
------------------
For any proposition :math:`P`, show :math:`\lnot \lnot \lnot P \to \lnot P`.

.. code-block:: lean4
  :name: triple_negation

  import Mathlib.Tactic

  example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
    sorry

Primes are two or odd
------------------------
Show that every prime :math:`p` satisfies :math:`p = 2` or :math:`p` is odd.
(There is a lemma in mathlib that says exactly this --- see if you can find it.)

.. code-block:: lean4
  :name: prime_two_or_odd

  import Mathlib.Tactic

  example (p : ℕ) : p.Prime → p = 2 ∨ p % 2 = 1 := by
    sorry

Consecutive primes and their sum
------------------------------------
Call two primes :math:`p < q` *consecutive* if no prime lies strictly between them. Work up to showing:
if :math:`p < q` are consecutive primes, neither equal to :math:`2`, then :math:`p + q` factors as a
product of *three* numbers each greater than :math:`1`.

Build the proof in stages:

(a) An even prime must equal :math:`2`.
(b) A sum of two odd numbers is even.
(c) If :math:`b < bc`, then :math:`c > 1`.
(d) A composite number :math:`k \ge 2` splits as :math:`k = ab` for some :math:`1 < a, b < k`.
(e) Put it together: since :math:`p, q \ne 2` are prime, they're both odd, so :math:`p + q = 2k` is even
    for some :math:`k` strictly between :math:`p` and :math:`q`; since :math:`k` can't be prime, it
    splits as :math:`k = bc` with :math:`b, c > 1`, giving :math:`p + q = 2 \cdot b \cdot c`.

.. code-block:: lean4
  :name: three_fac_of_sum_consecutive_primes

  import Mathlib.Tactic

  -- (a) an even prime must be 2
  lemma eq_two_of_even_prime {p : ℕ} (hp : p.Prime) (h_even : Even p) : p = 2 := by
    sorry

  -- (b) a sum of two odd numbers is even
  lemma even_of_odd_add_odd
      {a b : ℕ} (ha : ¬ Even a) (hb : ¬ Even b) :
      Even (a + b) := by
    sorry

  -- (c) if b < b * c, then c is at least 2
  lemma one_lt_of_nontrivial_factor
      {b c : ℕ} (hb : b < b * c) :
      1 < c := by
    sorry

  -- (d) a composite k ≥ 2 splits as a product of two smaller factors, each > 1
  lemma nontrivial_product_of_not_prime
      {k : ℕ} (hk : ¬ k.Prime) (two_le_k : 2 ≤ k) :
      ∃ a b, a < k ∧ b < k ∧ 1 < a ∧ 1 < b ∧ a * b = k := by
    sorry

  -- (e) the main theorem
  theorem three_fac_of_sum_consecutive_primes
      {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
      (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
      (consecutive : ∀ k, p < k → k < q → ¬ k.Prime) :
      ∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 := by
    sorry

The frog problem
===================
This one is the first problem from Mathcamp's 2012 qualifying quiz, formalized.

A *frog* lives on the lily pads numbered :math:`0, 1, 2, \dots` (the natural numbers). It starts on pad
:math:`0` at time :math:`0`, and it has some fixed step size :math:`s \in \mathbb{N}`: every second, it
jumps :math:`s` pads to the right.

.. math::

  \mathrm{location}(0) = 0 \qquad \mathrm{location}(n+1) = \mathrm{location}(n) + s

Work through the following:

(a) Show that a frog with step size :math:`s` is at position :math:`n \cdot s` at time :math:`n`.
(b) For every step size :math:`s` there is a frog that takes steps of size :math:`s` --- construct it.
(c) Conversely, every frog is *the* frog of its step size (a frog is determined entirely by its step size).
(d) **The quiz problem.** You get to check exactly one lily pad each second, without knowing the frog's
    step size in advance. Show that there is a strategy (a choice of which pad to check at each time
    :math:`n`) that is guaranteed to eventually catch the frog --- i.e. to check the very pad the frog is
    on at that moment --- no matter what step size the frog turns out to have.

.. code-block:: lean4
  :name: frog_problem

  import Mathlib.Tactic

  @[ext]
  structure Frog where
    -- A frog hangs out on the natural number line of lily pads
    location : ℕ → ℕ
    -- At time 0, it sits on location 0
    location_zero : location 0 = 0
    -- For some fixed step size,
    step_size : ℕ
    -- the frog jumps `step_size` units to the right each second
    step : ∀ n, location (n + 1) = location n + step_size

  -- (a)
  lemma frog_explicit_formula (f : Frog) :
      ∀ n, f.location n = n * f.step_size := by
    sorry

  -- (b)
  def frogOfStepSize (step_size : ℕ) : Frog where
    location := fun n => n * step_size
    location_zero := by sorry
    step_size := step_size
    step := by sorry

  -- (c)
  lemma frog_eq_frog_of_step_size (f : Frog) :
      f = frogOfStepSize f.step_size := by
    sorry

  -- (d) the quiz problem
  lemma catch_the_frog :
      ∃ (strategy : ℕ → ℕ),
      -- no matter how fast the frog travels,
      ∀ step_size,
      -- you'll eventually catch it
      ∃ catch_time > 0,
      strategy catch_time = (frogOfStepSize step_size).location catch_time := by
    sorry
