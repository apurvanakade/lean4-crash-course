.. _hint_2_mcsp:

Hint 2 for the math campers singing paradox
--------------------------------------------

Try 

.. code::

  by_cases h : ∃ bob : camper, ¬ singing bob
  obtain ⟨bob, key⟩ := h
  use bob
  push Not at h
