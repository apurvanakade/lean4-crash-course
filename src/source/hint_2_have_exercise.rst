.. _hint_2_have_exercise:

Hint 2 for the have exercise
-----------------------------------

Try 

.. code::

  intro h1 h2
  have h3 := Nat.dvd_sub h2 h1
  have h_one : 1 = (a + 1) - a

Once you've proved ``h_one``, use it to rewrite ``h3``.
