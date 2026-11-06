import Mathlib

theorem algebra_98 : 2*Real.sqrt (3-2*Real.sqrt 2) + Real.sqrt (17-12*Real.sqrt 2) = 1 := by 
  have h1 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    have h2 : (Real.sqrt 2 - 1) ^ 2 = (3 - 2 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    have h3 : 0 ≤ (Real.sqrt 2 - 1 : ℝ) := by
      have h4 : Real.sqrt 2 ≥ 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.lt_sqrt_of_sq_lt (show (1 : ℝ) ^ 2 < (2 : ℝ) by norm_num)]
      nlinarith
    rw [←h2]
    field_simp [Real.sqrt_sq h3]
  
  have h2 : Real.sqrt (17 - 12 * Real.sqrt 2) = (3 - 2 * Real.sqrt 2 : ℝ) := by
    have h3 : (3 - 2 * Real.sqrt 2 : ℝ) ^ 2 = (17 - 12 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    
    have h4 : (0 : ℝ) ≤ (3 - 2 * Real.sqrt 2 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2),
          Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)]
    
    rw [←h3]
    field_simp [Real.sqrt_sq h4]

  rw [h1, h2]

  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]