import Mathlib

theorem algebra_5972 : Real.sqrt (26 - 6 * Real.sqrt 17) = Real.sqrt 17 - 3 := by
  have h1 : (Real.sqrt 17 - 3 : ℝ) ^ 2 = 26 - 6 * Real.sqrt 17 := by
    have h2 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 17]
  have h3 : Real.sqrt 17 - 3 ≥ 0 := by
    have h4 : Real.sqrt 17 ≥ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
    have h5 : Real.sqrt 9 = 3 := by
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
    linarith [Real.sqrt_nonneg 17, h5]
  rw [← h1]
  field_simp [Real.sqrt_sq h3]
  all_goals nlinarith [Real.sqrt_nonneg 17]