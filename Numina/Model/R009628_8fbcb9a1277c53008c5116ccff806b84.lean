import Mathlib

theorem algebra_16804 {R r : ℝ} (hR : R = 10) (hr : r = 6) :
    Real.pi * (R^2 - r^2) = 64 * Real.pi := by
  rw [hR, hr]
  ring