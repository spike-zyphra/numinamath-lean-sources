import Mathlib

theorem algebra_128842 {R : ℝ} (hR : R > 0) (hR1 : R + 2 * R ^ 2 = 10.8) (hR2 : R + 2 * R ^ 2 + 16 = 100) :
    R = 23 := by
  nlinarith