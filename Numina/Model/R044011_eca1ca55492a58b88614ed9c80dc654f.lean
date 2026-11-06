import Mathlib

theorem algebra_161355 (x : ℝ) (hx : x = (45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) - (45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) :
    x = 2 * Real.sqrt 2 := by

  have h1 : Real.sqrt 2 > 0 := by
    positivity
  
  have h6 : x ^ 3 + 21 * x - 58 * Real.sqrt 2 = 0 := by
    rw [hx]
    have h7 : ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) ^ 3 = 45 + 29 * Real.sqrt 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    
    have h8 : ((45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) ^ 3 = 45 - 29 * Real.sqrt 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    
    have h9 : ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) * ((45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) = 7 := by
      have h10 : ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) * ((45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) = ((45 + 29 * Real.sqrt 2) * (45 - 29 * Real.sqrt 2)) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    
      rw [h10]
      have h11 : (45 + 29 * Real.sqrt 2) * (45 - 29 * Real.sqrt 2) = 343 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    
      rw [h11]
      have h12 : (343 : ℝ) ^ ((1 : ℝ) / 3) = 7 := by
        have h13 : (343 : ℝ) = (7 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [h13]
        have h14 : ((7 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = 7 := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        exact h14
      linarith
  
    nlinarith [sq_nonneg ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) - (45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) - 2 * Real.sqrt 2), sq_nonneg ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) + (45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) - 7 * Real.sqrt 2), sq_nonneg ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) + (45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)), sq_nonneg ((45 + 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3) - (45 - 29 * Real.sqrt 2) ^ ((1 : ℝ) / 3)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  
  have h7' : (2 * Real.sqrt 2) ^ 3 + 21 * (2 * Real.sqrt 2) - 58 * Real.sqrt 2 = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  
  have h13 : x = (2 * Real.sqrt 2) := by
    nlinarith [sq_nonneg (x - (2 * Real.sqrt 2)), sq_nonneg (x + (2 * Real.sqrt 2)), sq_nonneg (x), sq_nonneg ((2 * Real.sqrt 2)), sq_pos_of_pos (show 0 < Real.sqrt 2 by positivity), mul_pos (show (0 : ℝ) < Real.sqrt 2 by positivity) (show (0 : ℝ) < (1 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  linarith