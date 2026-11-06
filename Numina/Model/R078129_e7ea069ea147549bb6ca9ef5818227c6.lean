import Mathlib

theorem algebra_254168 : Real.sqrt (7 + 4 * Real.sqrt 3) + Real.sqrt (7 - 4 * Real.sqrt 3) = 4 := by
  have h1 : Real.sqrt (7 + 4 * Real.sqrt 3) = Real.sqrt 3 + 2 := by
    have h2 : (Real.sqrt 3 + 2) ^ 2 = 7 + 4 * Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h3 : 0 ≤ Real.sqrt 3 + 2 := by
      nlinarith [Real.sqrt_nonneg 3]
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  have h4 : Real.sqrt (7 - 4 * Real.sqrt 3) = 2 - Real.sqrt 3 := by
    have h5 : (2 - Real.sqrt 3) ^ 2 = 7 - 4 * Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : 0 ≤ (2 - Real.sqrt 3 : ℝ) := by
      have h7 : Real.sqrt 3 ≤ (2 : ℝ) := by
        rw [Real.sqrt_le_left]
        all_goals norm_num
        all_goals linarith [Real.sqrt_nonneg 3]
      linarith [Real.sqrt_nonneg 3]
    rw [← h5]
    field_simp [Real.sqrt_sq h6]
  rw [h1, h4]
  ring