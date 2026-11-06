import Mathlib

theorem algebra_14130 : Real.sqrt (37 - 20 * Real.sqrt 3) = 5 - 2 * Real.sqrt 3 := by
  have h1 : (5 - 2 * Real.sqrt 3) ^ 2 = 37 - 20 * Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : 5 - 2 * Real.sqrt 3 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [← h1]
  rw [Real.sqrt_sq]
  all_goals nlinarith [h2]