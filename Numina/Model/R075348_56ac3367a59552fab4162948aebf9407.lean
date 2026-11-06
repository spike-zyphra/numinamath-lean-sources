import Mathlib

theorem algebra_10555 (z : ℝ) (hz : 5 + 2 * z ≥ 0) (h : Real.sqrt (5 + 2 * z) = 11) :
    z = 58 := by
  have h1 : Real.sqrt (5 + 2 * z) ≥ 0 := by positivity
  have h2 : (Real.sqrt (5 + 2 * z)) ^ 2 = 11 ^ 2 := by
    rw [h]
  rw [Real.sq_sqrt hz] at h2
  nlinarith