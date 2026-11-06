import Mathlib

theorem algebra_252758 : (25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) = 5 := by
  have h1 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 = 25 + 5 * Real.sqrt 20 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      have h2 : Real.sqrt 20 ^ 2 = 20 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 20]
  
  have h1a : ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 = 25 - 5 * Real.sqrt 20 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      have h2 : Real.sqrt 20 ^ 2 = 20 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 20]
  
  have h2 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) * ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) = 5 := by
    have h3 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) * ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) = ((25 + 5 * Real.sqrt 20) * (25 - 5 * Real.sqrt 20 : ℝ)) ^ ((1 : ℝ) / 3) := by 
      rw [← Real.mul_rpow]
      all_goals
        have h4 : 0 ≤ (25 + 5 * Real.sqrt 20 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)]
        have h5 : 0 ≤ (25 - 5 * Real.sqrt 20 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num), sq_nonneg (Real.sqrt 20 - 2 : ℝ), sq_nonneg (Real.sqrt 20 - 3 : ℝ)]
        all_goals nlinarith
    have h6 : (25 + 5 * Real.sqrt 20 : ℝ) * (25 - 5 * Real.sqrt 20 : ℝ) = (125 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)]
    rw [h3, h6]
    have h7 : (125 : ℝ) ^ ((1 : ℝ) / 3) = 5 := by
      have h8 : (125 : ℝ) = 5 ^ (3 : ℝ) := by norm_num
      rw [h8]
      have h9 : ((5 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h9]
    linarith [h7]

  have h3 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 = 50 + 15 * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) := by
    have eq1 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 = ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 + ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) * ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3))) * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) := by
      ring
    rw [eq1, h1, h1a, h2]
    nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)]
  
  have h4 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) - 5) * (((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 2 + 5 * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) + 10) = 0 := by
    nlinarith [h3]

  have h5 : ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 2 + 5 * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) + 10 ≠ 0 := by
    nlinarith [sq_nonneg ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + 5 / 2), sq_nonneg ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) - (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)), sq_nonneg ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + 5), sq_nonneg ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)), sq_nonneg ((25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)), sq_nonneg (Real.sqrt 20 ^ 2 - 20)]
  
  have h6 : (25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) - 5 = 0 := by
    apply (mul_left_inj' (show ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) ^ 2 + 5 * ((25 + 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3) + (25 - 5 * Real.sqrt 20) ^ ((1 : ℝ) / 3)) + 10 ≠ 0 by exact h5)).mp
    linarith [h4]
  
  linarith [h6]