import Mathlib

theorem algebra_95129 (t ins outs : ℝ) (ht : t > 0) :
(20 * t - 18 * t) > 0 := by
  have h1 : 20 * t - 18 * t = 2 * t := by
    ring
  rw [h1]
  linarith