.. _day4:

**************************
Sqrt 2 is irrational
**************************

Today we will teach Lean that :math:`\sqrt{2}` is irrational.
Let us start by reviewing some concepts we encountered yesterday.

Implicit arguments
====================
Consider the following theorem which says that the smallest non-trivial factor of a natural number greater than 1 is a prime number. 

.. code::

  Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime

It needs only one argument, namely a term of type ``n ≠ 1``.
But we have not told Lean what ``n`` is!
That's because if we pass a term, say ``hp : 2 ≠ 1`` to ``Nat.minFac_prime`` then from ``hp`` Lean can infer that ``n = 2``.
``n`` is called an *implicit* argument.
An argument is made implicit by using curly brackets ``{`` and ``}`` instead of the usual ``(`` and ``)`` while defining the theorem.

.. code::

  theorem Nat.minFac_prime {n : ℕ} (hne1 : n ≠ 1) : (Nat.minFac n).Prime := ...

Sometimes the notation is ambiguous and Lean is unable to infer the implicit arguments.
In such a case, you can force all the arguments to become explicit by putting an ``@`` symbol in front of the theorem. For example,

.. code::

  @Nat.minFac_prime : (n : ℕ) → n ≠ 1 → (Nat.minFac n).Prime

Use this sparingly as this makes the proof very hard to read and debug.


The two haves 
===============

We have seen two slightly different variants of the ``have`` tactic. 

.. code:: 

  have hq := ... 
  have hq : ...

In the first case, we are defining ``hq`` to be the term on the right hand side. 
In the second case, we are saying that we do not know what the term ``hq`` is but we know it's type.

Let's consider the example of ``Nat.minFac_prime`` again.
Suppose we want to conclude that the smallest factor of 10 is a prime.
We will need a term of type ``(Nat.minFac 10).Prime``.
If this is the target, we can use ``apply Nat.minFac_prime``.
If not, we need a proof of ``10 ≠ 1`` to provide as input to ``Nat.minFac_prime``.
For this we'll use

.. code::

  have ten_ne_one : 10 ≠ 1

which will open up a goal with target ``10 ≠ 1``.
If on the other hand, you have another hypothesis, say ``f : P →  (10 ≠ 1)`` and a term ``hp : P``, then

.. code::

  have ten_ne_one := f hp

will immediately create a term of type ``10 ≠ 1``. More generally, remember that 

1. "``:=``" stands for definition. ``x := ...`` means that ``x`` is defined to be the right hand side.
2. "``:``" is a way of specifying type. ``x : ...`` means that the type of ``x`` is the right hand side. 
3. "``=``" is only ever used in propositions and has nothing to do with terms or types.


Sqrt(2) is irrational
=======================
We will show that there do not exist non-zero natural numbers ``m`` and ``n`` such that 

.. code:: 

  2 * m ^ 2 = n ^ 2  -- (*)

The crux of the proof is very easy. 
You simply have to start with the assumption that ``m`` and ``n`` are coprime *without any loss of generality* and derive a contradiction.
But proving that *without loss of generality* is a valid argument requires quite a bit of effort.
This proof is broken down into several parts. 
The first two parts prove ``(*)`` assuming that ``m`` and ``n`` are coprime.
The rest of the parts prove the *without loss of generality* part.

For this problem, you'll need the following definitions.

  * ``m.gcd n : ℕ`` is the gcd of ``m`` and ``n``.
  * ``m.Coprime n`` is defined to be the proposition ``m.gcd n = 1``.

The descriptions of the library theorems you'll need are included as comments.
Have fun!

Lemmas for proving (*) assuming m and n are coprime.
------------------------------------------------------------------------------
.. code:: lean4

  import Mathlib.Tactic

  --BEGIN--
  -- Nat.Prime.dvd_of_dvd_pow : p.Prime → p ∣ m ^ n → p ∣ m
  lemma two_dvd_of_two_dvd_sq {k : ℕ}
      (hk : 2 ∣ k ^ 2) :
      2 ∣ k := by
    sorry

  -- to switch the target from ``P = Q`` to ``Q = P``,
  -- use the tactic ``symm``
  lemma division_lemma_n {m n : ℕ}
      (hmn : 2 * m ^ 2 = n ^ 2) :
      2 ∣ n := by
    sorry

  lemma div_2 {m n : ℕ} (hnm : 2 * m = 2 * n) : (m = n) := by
    linarith

  lemma division_lemma_m {m n : ℕ}
      (hmn : 2 * m ^ 2 = n ^ 2) :
      2 ∣ m := by
    sorry
  --END--

Prove (*) assuming m and n are coprime.
------------------------------------------------------------------------------

.. code:: lean4

  import Mathlib.Tactic

  lemma two_dvd_of_two_dvd_sq {k : ℕ}
      (hk : 2 ∣ k ^ 2) :
      2 ∣ k := by
    sorry

  lemma division_lemma_n {m n : ℕ}
      (hmn : 2 * m ^ 2 = n ^ 2) :
      2 ∣ n := by
    sorry

  lemma division_lemma_m {m n : ℕ}
      (hmn : 2 * m ^ 2 = n ^ 2) :
      2 ∣ m := by
    sorry

  -- Assume that everything above this line is true.

  --BEGIN--

  -- If ``1 < d``, ``d ∣ m``, and ``d ∣ n``, then ``d ∣ Nat.gcd m n`` (via
  -- ``Nat.dvd_gcd``), and since ``m.Coprime n`` means ``Nat.gcd m n = 1``,
  -- this contradicts ``1 < d``.

  theorem sqrt2_irrational' :
      ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
    rintro ⟨m, n, hmn, h_cop⟩
    -- rintro lets you destructure the hypothesis as you introduce it
    -- you get the brackets by typing ``\langle`` and ``\rangle``
    sorry

  --END--

  

Lemmas for proving (*) assuming m ≠ 0
------------------------------------------------------------------------------
.. code:: lean4

  import Mathlib.Tactic

  theorem sqrt2_irrational' :
      ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
    sorry

  -- Assume that everything above this line is true.

  --BEGIN--

  lemma ne_zero_ge_zero {n : ℕ}
      (hne : n ≠ 0) :
      (0 < n) := by
    contrapose! hne
    sorry

  -- Nat.pow_pos : 0 < p → 0 < p ^ n  (n is inferred automatically)
  lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n ^ 2) := by
    sorry

  lemma cancellation_lemma {k m n : ℕ}
      (hk_pos : 0 < k ^ 2)
      (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) :
      2 * m ^ 2 = n ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hk_pos
    ring_nf
    ring_nf at hmn
    linarith [hmn]

  --END--


Prove (*) assuming m ≠ 0
------------------------------------------------------------------------------
.. code:: lean4

  import Mathlib.Tactic

  theorem sqrt2_irrational' :
      ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.Coprime n := by
    sorry

  lemma ne_zero_ge_zero {n : ℕ}
      (hne : n ≠ 0) :
      (0 < n) := by
    contrapose! hne
    sorry

  lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n ^ 2) := by
    sorry

  lemma cancellation_lemma {k m n : ℕ}
      (hk_pos : 0 < k ^ 2)
      (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) :
      2 * m ^ 2 = n ^ 2 := by
    sorry

  -- Assume that everything above this line is true.

  --BEGIN--

  -- Nat.gcd_pos_of_pos_left : 0 < m → 0 < Nat.gcd m n
  -- Nat.gcd_pos_of_pos_right : 0 < n → 0 < Nat.gcd m n
  -- Nat.exists_coprime : ∀ (m n : ℕ), ∃ m' n', m'.Coprime n' ∧ m = m' * m.gcd n ∧ n = n' * m.gcd n

  theorem wlog_coprime :
      (∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0) →
      (∃ (m' n' : ℕ), 2 * m' ^ 2 = n' ^ 2 ∧ m'.Coprime n') := by
    rintro ⟨m, n, hmn, hme0⟩
    set k := m.gcd n with hk
    -- might be useful to declutter
    -- you can replace all the ``m.gcd n`` with ``k`` using ``rw [← hk]`` if needed
    sorry

  theorem sqrt2_irrational'' :
      ¬ ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m ≠ 0 := by
    sorry

  --END--

