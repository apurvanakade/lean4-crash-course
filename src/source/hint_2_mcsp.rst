.. _hint_2_mcsp:

Hint 2 for the math campers singing paradox
--------------------------------------------

Try 

.. code::

  by_cases h : ∃ bob : camper, ¬ singing bob
  -- first goal: h : ∃ bob : camper, ¬ singing bob
  obtain ⟨bob, key⟩ := h
  use bob
  -- ... finish the first goal ...
  -- second goal: h : ¬ ∃ bob : camper, ¬ singing bob
  push Not at h
