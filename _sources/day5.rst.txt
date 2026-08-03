.. _day5:

***************************
Bits & Pieces
***************************

Namespaces
===========

Lean provides us with the ability to group definitions into nested, hierarchical *namespaces*:

.. code-block:: lean4

  namespace vmcsp
    def tau := "TAU on M-Th from 1-3"
    #eval tau
  end vmcsp

  def tau := "no TAU on F"
  #eval tau
  #eval vmcsp.tau

  open vmcsp

  -- #eval tau  -- error: `tau` is now ambiguous between `_root_.tau` and `vmcsp.tau`
  #eval vmcsp.tau

When we declare that we are working in the namespace ``vmcsp``, every identifier we declare has a full name with prefix "``vmcsp``".
Within the namespace, we can refer to identifiers by their shorter names, but once we end the namespace, we have to use the longer names.

The ``open`` command brings the shorter names into the current context. Often, when we import a theory file, we will want to open one or more of the namespaces it contains, to have access to the short identifiers.
Further, if ``x`` is a term of type ``Nat`` and ``f`` is a term defined in namespace ``Nat`` then ``Nat.f x`` can be shortened to ``x.f``.
Note that ``ℕ`` is just another notation for ``Nat``.

Coercions 
===========
In type theory every term has a type and two terms of different types cannot be equal to each other.
This makes it impossible to write statements like ``|m|^2 = m^2`` where ``m : ℤ`` and ``|m| : ℕ`` is the absolute value of ``m``.
But in math, we do want this statement to be true!
The roundabout way to deal with this is through *coercions*.
Lean will coerce the above equality to live entirely in integers as ``↑|m|^2 = m^2``.
This is done using an injective function ``ℕ → ℤ``.

Sometimes it is possible (and necessary) to get rid of the coercions. 
For example, say we start out with ``↑|m|^2 = m^2`` and eventually reduce it to ``↑|m|^2 = ↑1``.
The tactic for getting rid of coercions is ``norm_cast`` which will reduce the above expression to ``|m|^2 = 1``.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``norm_cast``
    - ``norm_cast`` tries to clear out coercions.

      ``norm_cast at hp`` tries to clear out coercions at the hypothesis ``hp``.


.. code:: lean4

  import Mathlib.Tactic

  theorem sqrt2_irrational_nat :
      ¬ ∃ (m n : ℕ), 2 * (m * m) = (n * n) ∧ m ≠ 0 := by
    sorry

  -- Assume the above theorem

  lemma num_2 : (2 : ℚ).num = 2 := by
    norm_num

  lemma den_2 : (2 : ℚ).den = 1 := by
    norm_num

  -- q.den = denominator of q (valued in ℕ)
  -- q.num = numerator of q (valued in ℤ)
  --
  -- for integer m,
  -- m.natAbs = absolute value of m (valued in ℕ)
  --
  -- Rat.mul_self_den : ∀ (q : ℚ), (q * q).den = q.den * q.den
  -- Rat.mul_self_num : ∀ (q : ℚ), (q * q).num = q.num * q.num
  -- Int.natAbs_mul_self' : ∀ (a : ℤ), ↑(a.natAbs) * ↑(a.natAbs) = a * a
  -- Rat.den_nz : ∀ (q : ℚ), q.den ≠ 0

  -- Use ``simp at hp`` (or, interactively, ``simp? at hp``) to commute
  -- products with coercions. See the goal window!

  theorem sqrt2_irrational :
      ¬ (∃ q : ℚ, 2 = q * q) := by
    rintro ⟨q, key⟩
    have clear_denom := Rat.eq_iff_mul_eq_mul.mp key
    sorry

Type classes
===========================
Type classes are used to construct complex mathematical structures. 
Any family of types can be marked as a type class. 
We can then declare particular elements of a type class to be instances.
You can think of a type class as "template" for constructing particular instances.

Consider the example of groups.
A group is defined as a type class with the following attributes.

.. code::

  structure Group : Type u → Type u
  fields:
  Group.mul : {α : Type u} → [c : Group α] → α → α → α
  Group.mul_assoc : ∀ {α : Type u} [c : Group α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  Group.one : {α : Type u} → [c : Group α] → α
  Group.one_mul : ∀ {α : Type u} [c : Group α] (a : α), 1 * a = a
  Group.mul_one : ∀ {α : Type u} [c : Group α] (a : α), a * 1 = a
  Group.inv : {α : Type u} → [c : Group α] → α → α
  Group.inv_mul_cancel : ∀ {α : Type u} [c : Group α] (a : α), a⁻¹ * a = 1

If you look at the `source code <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Group/Defs.lean>`__ you'll see that ``class Group`` is built gradually by extending multiple classes
(the real hierarchy in mathlib4 has a few more intermediate steps than shown here, to support both additive and multiplicative notation, but the idea is the same).

.. code::

  class One  (α : Type u) where
    one : α
  -- a group has an identity element

  class Mul  (α : Type u) where
    mul : α → α → α
  -- a group has multiplication

  class Inv  (α : Type u) where
    inv : α → α
  -- a group has an inverse function

  class Semigroup (G : Type u) extends Mul G where
    mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  -- the multiplication is associative

  class Monoid (M : Type u) extends Semigroup M, One M where
    one_mul : ∀ a : M, 1 * a = a
    mul_one : ∀ a : M, a * 1 = a
  -- multiplication by one is trivial

  class Group (α : Type u) extends Monoid α, Inv α where
    inv_mul_cancel : ∀ a : α, a⁻¹ * a = 1
  -- every element has an inverse

To define an arbitrary group ``G`` we first create it as a type ``G : Type`` and then assume it is a group using
``[Group G]``.
You can also prove that existing types are instances of ``Group`` using the ``instance`` keyword.
Type classes allow us to prove theorems in great generality.
For example, any theorem about groups can immediately be applied to integers once we show that integers are an instance of ``Group``.
If you look at `Mathlib.Algebra.Group.Int <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Group/Int.lean>`__
you'll see the code that proves ``ℤ`` is an instance of several type classes.

.. code:: lean4

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


Final remarks
=================

That's a wrap! Over the last five days you went from wrangling ``P → Q`` with ``intro`` and ``exact`` to
building type classes and proving that there are infinitely many primes and that :math:`\sqrt{2}` is
irrational. That is genuinely research-level formalization, and you did it in a week.

The tactics you practiced --- ``intro``, ``have``, ``obtain``, ``rw``, ``norm_num``, and friends --- are
exactly the tactics used to formalize serious mathematics in `mathlib <https://leanprover-community.github.io/>`__,
a rapidly growing, community-maintained library that by now covers a huge swath of undergraduate and
graduate mathematics.

If you want to keep going:

#. Finish the `Natural Number Game <https://adam.math.hhu.de/#/g/leanprover-community/NNG4>`__ if you haven't already.
#. Work through `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`__ for a more systematic treatment of the theory behind what we did.
#. Pick a theorem you like and try to formalize it. `100 theorems in Lean <https://leanprover-community.github.io/100.html>`__ is a good source of inspiration, and the `mathlib4 repository <https://github.com/leanprover-community/mathlib4>`__ is a good place to look for the building blocks you'll need.
#. Stick around on the `Lean Zulip chat group <https://leanprover.zulipchat.com/>`__ --- people there are very welcoming to newcomers, and it's the best way to find out what the community is working on.

Thanks for spending the week with us, and good luck with your future proofs!