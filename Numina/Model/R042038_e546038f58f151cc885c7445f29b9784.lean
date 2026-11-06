import Mathlib

theorem algebra_20401 {b : ℝ} (h : (3 + Real.sqrt 5)^2 - 3 * (3 + Real.sqrt 5) + b = 0) :
    b = -3 * Real.sqrt 5 - 5 := by
  have h1 : Real.sqrt 5 ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h2 : (3 + Real.sqrt 5) ^ 2 = 14 + 6 * Real.sqrt 5 := by
    nlinarith [h1]
  have h3 : (3 * (3 + Real.sqrt 5) : ℝ) = 9 + 3 * Real.sqrt 5 := by
    ring
  rw [h2, h3] at h
  linarith