.. _symbols:


Pretty Symbols in Lean
=================================

To produce a pretty symbol in Lean, type the *editor shortcut* followed by space or tab. 

.. list-table::
  :widths: 20 35 45
  :header-rows: 1

  * - Unicode 
    - Editor Shortcut 
    - Definition 

  * - ∀
    - ``\forall``
    - for all quantifier

  * - ∃ 
    - ``\exists``
    - there exists quantifier

  * - →
    - ``\to``
    - function or implies

  * - ↔
    - ``\iff``
    - if and only if

  * - ∧
    - ``\and``
    - and operator

  * - ∨ 
    - ``\or``
    - or operator

  * - ¬
    - ``\not`` 
    - negation operator

  * - ≠
    - ``\ne``
    - not equal to

  * - ≤
    - ``\le``
    - less than or equal to

  * - ≥
    - ``\ge``
    - greater than or equal to

  * - ∣
    - ``\mid``
    - divisibility [#f1]_

  * - ∈
    - ``\in``
    - is an element of

  * - ℕ
    - ``\nat``
    - type of natural numbers

  * - ℤ
    - ``\int``
    - type of integers

  * - ℚ
    - ``\Q``
    - type of rational numbers

  * - ℝ
    - ``\R``
    - type of real numbers

  * - ↑
    - ``\u``
    - coercion from one type to another (e.g. ``ℕ → ℤ``)

  * - ⟨ ⟩
    - ``\langle`` ``\rangle``
    - angle brackets, used by ``obtain``, ``use``, ``refine`` and for pairs of terms (also ``\<`` and ``\>``)

  * - .
    - ``.`` followed by a space
    - focuses on the first goal: the tactics indented after it must close it

  * - ←
    - ``\l`` 
    - used by the ``rw`` tactic (also ``\leftarrow``)

  * - ∘
    - ``\circ``
    - composition of functions

  * - ∑
    - ``\sum``
    - sum over a range

  * - ⁻¹
    - ``\inv``
    - multiplicative inverse

  * - α
    - ``\a``
    - Greek letter alpha, often used as a name for a type (``\b`` gives β, and so on)


.. rubric:: Footnotes

.. [#f1] Be very careful! The symbol for divisibility is not the ``|`` symbol on your keyboard. Lean will through a cryptic error if you use it.