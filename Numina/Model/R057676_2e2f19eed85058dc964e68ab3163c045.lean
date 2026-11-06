import Mathlib

theorem algebra_231367 : (1/4) * (Real.sqrt 5 - 1) * Real.sqrt (6 + 2 * Real.sqrt 5) = 1 := by 
  have h1 : Real.sqrt (6 + 2 * Real.sqrt 5) = Real.sqrt 5 + 1 := by
    have h2 : (Real.sqrt 5 + 1) ^ 2 = 6 + 2 * Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h3 : 0 ≤ (6 + 2 * Real.sqrt 5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5]
    have h4 : 0 ≤ (Real.sqrt 5 + 1 : ℝ) := by
      positivity
    have h5 : Real.sqrt (6 + 2 * Real.sqrt 5) = Real.sqrt ( (Real.sqrt 5 + 1) ^ 2 ) := by
      rw [h2]
    rw [h5]
    rw [Real.sqrt_sq (by linarith [Real.sqrt_nonneg 5]) ]
  rw [h1]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]