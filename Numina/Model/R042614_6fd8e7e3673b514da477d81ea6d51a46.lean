import Mathlib

theorem algebra_18900 (r : ℝ) (hr : r = 2) :
    π * (2 * r)^2 - π * r^2 = 12 * π := by
  rw [hr]
  ring