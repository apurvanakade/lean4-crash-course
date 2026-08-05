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

-- the frog that takes steps of size `step_size`
def frogOfStepSize (step_size : ℕ) : Frog where
  location := fun n => n * step_size
  location_zero := by simp
  step_size := step_size
  step := by intro n; ring

-- (b)
lemma frog_eq_frog_of_step_size (f : Frog) :
    f = frogOfStepSize f.step_size := by
  sorry

-- (c) the quiz problem
lemma catch_the_frog :
    ∃ (strategy : ℕ → ℕ),
    -- no matter how fast the frog travels,
    ∀ step_size,
    -- you'll eventually catch it
    ∃ catch_time > 0,
    strategy catch_time = (frogOfStepSize step_size).location catch_time := by
  sorry