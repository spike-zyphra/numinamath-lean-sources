import Mathlib
open Real
theorem algebra_94594 {x : ℝ} (hx : x ≥ 100) :
(1 - 10 / 100) * x > (1 - 20 / 100) * x ∧ (1 - 10 / 100) * x > (1 - 18 / 100) * (x - 100) := by
  constructor
  · -- Show that (1 - 10 / 100) * x > (1 - 20 / 100) * x
    nlinarith
  · -- Show that (1 - 10 / 100) * x > (1 - 18 / 100) * (x - 100)
    nlinarith