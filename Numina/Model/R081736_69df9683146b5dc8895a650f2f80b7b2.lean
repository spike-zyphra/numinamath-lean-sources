import Mathlib

theorem algebra_219689 : √(13 + 4 * √3) + √(13 - 4 * √3) = 4 * √3 := by
  have h1 : √(13 + 4 * √3) = 2 * √3 + 1 := by
    have h2 : (2 * √3 + 1) ^ 2 = 13 + 4 * √3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h3 : 2 * √3 + 1 ≥ 0 := by
      positivity
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  
  have h4 : √(13 - 4 * √3) = 2 * √3 - 1 := by
    have h5 : (2 * √3 - 1) ^ 2 = 13 - 4 * √3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h6 : 2 * √3 - 1 ≥ 0 := by
      have h5' : 2 * √3 ≥ 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      linarith [h5']
    
    rw [← h5]
    field_simp [Real.sqrt_sq h6]

  rw [h1, h4]
  ring