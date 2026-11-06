import Mathlib

theorem algebra_257289 : Real.sqrt (7 + 2 * Real.sqrt 6) - Real.sqrt (7 - 2 * Real.sqrt 6) = 2 := by
  have h1 : Real.sqrt (7 + 2 * Real.sqrt 6) = 1 + Real.sqrt 6 := by
    have h12 : (1 + Real.sqrt 6) ^ 2 = 7 + 2 * Real.sqrt 6 := by
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6: ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 6]
    have h13 : 1 + Real.sqrt 6 ≥ 0 := by
      have h4 : Real.sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
      linarith [Real.sqrt_nonneg 6]
    rw [← h12]
    field_simp [Real.sqrt_sq h13]
    all_goals nlinarith [Real.sqrt_nonneg 6]
  have h2 : Real.sqrt (7 - 2 * Real.sqrt 6) = Real.sqrt 6 - 1 := by
    have h22 : (Real.sqrt 6 - 1) ^ 2 = 7 - 2 * Real.sqrt 6 := by 
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6: ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 6]
    have h23 : Real.sqrt 6 - 1 ≥ 0 := by
      have h5 : 1 ≤ Real.sqrt 6 := by
        rw [Real.le_sqrt] <;> (norm_num)
        all_goals nlinarith [Real.sqrt_nonneg 6]
      linarith [Real.sqrt_nonneg 6]
      all_goals linarith [Real.sqrt_nonneg 6]
    rw [← h22]
    field_simp [Real.sqrt_sq h23]
    all_goals nlinarith [Real.sqrt_nonneg 6]
  rw [h1, h2]
  all_goals nlinarith [Real.sqrt_nonneg 6]
  all_goals try { norm_num }
  all_goals try { linarith [Real.sqrt_nonneg 6] }