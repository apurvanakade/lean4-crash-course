.. _hint_2_barber_paradox:

Hint 2 for the barber paradox
-----------------------------------

Try

.. code::

    by_contra a
    have b := a barber
    obtain ⟨b1, b2⟩ := b
    by_cases h : shaves barber barber
