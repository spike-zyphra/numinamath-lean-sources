import Mathlib

open Real

theorem algebra_96166 {x : ℝ} (hx : x = sqrt (1 + sqrt (1 + sqrt 1))) :
    (x ^ 4) = 3 + 2 * sqrt 2 := by
  have h1 : sqrt 1 = (1 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : sqrt (1 + sqrt 1) = Real.sqrt 2 := by
    rw [h1]
    norm_num
  have h3 : x = Real.sqrt (1 + Real.sqrt 2) := by
    rw [hx]
    rw [h2]
    all_goals norm_num
  have h4 : x ^ 2 = 1 + Real.sqrt 2 := by
    rw [h3]
    rw [Real.sq_sqrt]
    positivity
  have h5 : x ^ 4 = (x ^ 2) ^ 2 := by
    ring
  have h6 : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  rw [h5, h4, h6]