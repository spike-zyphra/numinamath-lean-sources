import Mathlib

theorem algebra_11807 : Real.sqrt 3 * 3 ^ ((1 : ℝ) / 2) + 12 / 3 * 2 - 4 ^ ((3 : ℝ) / 2) = 3 := by
  have h1 : Real.sqrt 3 = (3 : ℝ) ^ ((1 : ℝ) / 2) := by 
    rw [Real.sqrt_eq_rpow]

  have h2 : Real.sqrt 3 * (3 : ℝ) ^ ((1 : ℝ) / 2) = 3 := by 
    rw [h1]
    
    have h3 : ((3 : ℝ) ^ ((1 : ℝ) / 2)) * (3 : ℝ) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals norm_num
      all_goals positivity
    rw [h3]
    all_goals norm_num
    all_goals positivity
  
  have h5 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
    have h6 : (4 : ℝ) ^ ((3 : ℝ) / 2) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) := by 
      norm_num
    rw [h6]
    
    have h7 : ((2 : ℝ) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = (2 : ℝ) ^ (2 * (3 / 2 : ℝ)) := by 
      rw [← Real.rpow_mul]
      ring_nf 
      all_goals positivity
    rw [h7]
    
    have h8 : (2 : ℝ) ^ (2 * (3 / 2 : ℝ)) = (2 : ℝ) ^ (3 : ℝ) := by 
      norm_num 
      <;> ring_nf
      <;> norm_num 
    rw [h8]
    
    norm_num

  have h4 : Real.sqrt 3 * (3 : ℝ) ^ ((1 : ℝ) / 2) = 3 := h2

  rw [h4, h5]
  norm_num
  all_goals linarith
  all_goals positivity