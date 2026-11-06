import Mathlib

open Real

theorem algebra_9803 : Real.sqrt (143 + 14 * Real.sqrt 90) = 3 * Real.sqrt 5 + 7 * Real.sqrt 2 := by
  have h1 : Real.sqrt 90 = 3 * Real.sqrt 10 := by
    calc
      Real.sqrt 90 = Real.sqrt (9 * 10) := by norm_num
      _ = Real.sqrt (3^2 * 10) := by norm_num
      _ = Real.sqrt (3^2) * Real.sqrt 10 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (3 : ℝ) * Real.sqrt 10 := by rw [Real.sqrt_sq (by norm_num)]

  have h2 : 143 + 14 * Real.sqrt 90 = (3 * Real.sqrt 5 + 7 * Real.sqrt 2) ^ 2 := by
    rw [h1]
    have h3 : Real.sqrt 10 = Real.sqrt 5 * Real.sqrt 2 := by
      calc 
        Real.sqrt 10 = Real.sqrt (5 * 2) := by norm_num
        _ = Real.sqrt 5 * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num)]

    rw [h3]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
    
  have h5 : 0 ≤ (3 * Real.sqrt 5 + 7 * Real.sqrt 2 : ℝ) := by 
    positivity

  rw [h2]
  rw [Real.sqrt_sq (show 0 ≤ (3 * Real.sqrt 5 + 7 * Real.sqrt 2 : ℝ) by positivity)]
  all_goals positivity