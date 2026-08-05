import Mathlib.Tactic

@[ext]
structure Frog where
  -- A frog hangs out on the natural number line of lily pads
  location : ℕ → ℕ
  -- At time 0, it sits on location 0
  location_zero : location 0 = 0
  -- For some fixed step size,
  step_size : ℕ
  -- the frog jumps `step_size` units to the right each second.
  step : ∀ n, location (n + 1) = location n + step_size

lemma frog_explicit_formula (f : Frog) :
    -- Show that the position of the frog at time n is n * step_size.
    ∀ n, f.location n = n * f.step_size := by
  intro n
  induction n with
  | zero =>
    -- At time `0` the frog is at `0`, and `0 = 0 * step_size`.
    rw [f.location_zero]; norm_num
  | succ d hd =>
    -- `f.location (d + 1) = f.location d + step_size`; substitute the induction hypothesis `hd`.
    rw [f.step, hd]; ring

-- We can define a frog just by giving its step size
def frogOfStepSize (step_size : ℕ) : Frog where
  location := fun n => n * step_size
  location_zero := by simp
  step_size := step_size
  step := by intro n; ring

-- and every frog can be defined in this way
lemma frog_eq_frog_of_step_size (f : Frog) :
    f = frogOfStepSize f.step_size := by
  -- Two frogs are equal iff they agree at every time `n` (and have the same step size).
  ext n
  · -- Positions agree, by the explicit formula proved above.
    rw [frog_explicit_formula]; simp [frogOfStepSize]
  · -- Step sizes agree trivially, by definition of `frogOfStepSize`.
    simp [frogOfStepSize]

lemma catch_the_frog :
    -- Show that there is a way to check one lily pad each second
    ∃ (strategy : ℕ → ℕ),
    -- so that no matter how fast the frog travels,
    ∀ step_size,
    -- you'll eventually catch it.
    ∃ catch_time > 0,
    strategy catch_time = (frogOfStepSize step_size).location catch_time := by
  -- Strategy: at time `n`, check lily pad `n * (n - 1)`.
  use fun n => n * (n - 1)
  -- Fix an arbitrary step size `k`.
  intro k
  -- We claim the frog is caught at time `k + 1`.
  use k + 1
  constructor
  · -- `k + 1 > 0` trivially.
    exact Nat.succ_pos k
  · -- At time `k + 1`, both the strategy and the frog are at `k * (k + 1)`.
    simp [frogOfStepSize]
