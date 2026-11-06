import Mathlib

theorem algebra_4215 {a b c : ℝ} (h₀ : a - b = 1 / (2 - √3)) (h₁ : b - c = 1 / (2 + √3)) :
    a^2 + b^2 + c^2 - a * b - b * c - c * a = 15 := by

  have h2 : a - b = 2 + Real.sqrt 3 := by
    rw [h₀]
    have h3 : (2 - Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h3]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have h3 : b - c = 2 - Real.sqrt 3 := by
    rw [h₁]
    have h4 : (2 + Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h4]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have h4 : a - c = 4 := by
    nlinarith [h2, h3]

  nlinarith [sq_nonneg (a - b - (2 + Real.sqrt 3)), sq_nonneg (b - c - (2 - Real.sqrt 3)), sq_nonneg (a - c - 4), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]