import Mathlib

theorem algebra_8032 {x : ℝ} (hx : x = √(4 + 2 * √3) + √(4 - 2 * √3)) : x = 2 * √3 := by
  rw [hx]
  have h1 : Real.sqrt (4 + 2 * Real.sqrt 3) = 1 + Real.sqrt 3 := by
    have h4 : (1 + Real.sqrt 3) ^ 2 = (4 + 2 * Real.sqrt 3) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h5 : (1 + Real.sqrt 3) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3]
    rw [← h4]
    field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ (4 + 2 * Real.sqrt 3) by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]), h5]
    all_goals nlinarith [Real.sqrt_nonneg 3]
  
  have h2 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
    have h6 : (Real.sqrt 3 - 1) ^ 2 = (4 - 2 * Real.sqrt 3) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h7 : (Real.sqrt 3 - 1 : ℝ) ≥ 0 := by
      have h3 : Real.sqrt 3 ≥ 1 := by
        have h4 : Real.sqrt 3 ≥ Real.sqrt 1 := by apply Real.sqrt_le_sqrt (by norm_num)
        have h5 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
        linarith [h4, h5]
      nlinarith [Real.sqrt_nonneg 3]
  
    rw [← h6]
    field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ (4 - 2 * Real.sqrt 3) by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]), h7]
    all_goals nlinarith [Real.sqrt_nonneg 3]
  
  rw [h1, h2]
  ring
  all_goals linarith [Real.sqrt_nonneg 3]