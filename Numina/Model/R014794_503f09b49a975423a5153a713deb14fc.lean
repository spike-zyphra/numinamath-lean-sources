import Mathlib

theorem algebra_312482 : (Real.sqrt (3 + 2 * Real.sqrt 2)) / (Real.sqrt (17 + 12 * Real.sqrt 2)) -
    (Real.sqrt (3 - 2 * Real.sqrt 2)) / (Real.sqrt (17 - 12 * Real.sqrt 2)) = -2 := by 
  have h1 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
    have h2 : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h3 : 0 ≤ Real.sqrt 2 + 1 := by 
      have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
    rw [← h2]
    field_simp [Real.sqrt_sq, h3]
  
  have h4 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by 
    have h5 : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    have h6 : 0 ≤ Real.sqrt 2 - 1 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show 1 ≤ (2 : ℝ) by norm_num)]
    
    rw [← h5]
    field_simp [Real.sqrt_sq, h6]

  have h7 : Real.sqrt (17 + 12 * Real.sqrt 2) = 3 + 2 * Real.sqrt 2 := by 
    have h8 : (3 + 2 * Real.sqrt 2 : ℝ) ^ 2 = 17 + 12 * Real.sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    have h9 : 0 ≤ (3 + 2 * Real.sqrt 2 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    rw [← h8]
    field_simp [Real.sqrt_sq, h9]

  have h10 : Real.sqrt (17 - 12 * Real.sqrt 2) = 3 - 2 * Real.sqrt 2 := by 
    have h11 : (3 - 2 * Real.sqrt 2 : ℝ) ^ 2 = 17 - 12 * Real.sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    have h12 : 0 ≤ (3 - 2 * Real.sqrt 2 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show 1 ≤ (2 : ℝ) by norm_num)]
    
    rw [← h11]
    field_simp [Real.sqrt_sq, h12]

  rw [h1, h4, h7, h10]

  have h13 : (Real.sqrt 2 + 1 : ℝ) / (3 + 2 * Real.sqrt 2 : ℝ) = Real.sqrt 2 - 1 := by 
    have h14 : (3 + 2 * Real.sqrt 2 : ℝ) ≠ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    field_simp [h14]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have h14 : (Real.sqrt 2 - 1 : ℝ) / (3 - 2 * Real.sqrt 2 : ℝ) = Real.sqrt 2 + 1 := by
    have h15 : (3 - 2 * Real.sqrt 2 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    
    field_simp [h15]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  rw [h13, h14]
  nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]