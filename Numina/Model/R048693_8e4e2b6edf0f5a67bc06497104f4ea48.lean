import Mathlib

open Real

theorem algebra_328122 : sqrt (2 * (6 - 2 * sqrt 3 - 2 * sqrt 5 + sqrt 15)) = -2 + sqrt 3 + sqrt 5 := by
  have h1 : 2 * (6 - 2 * sqrt 3 - 2 * sqrt 5 + sqrt 15) = (-2 + sqrt 3 + sqrt 5) ^ 2 := by
    nlinarith [sq_nonneg (sqrt 3 - 1), sq_nonneg (sqrt 5 - 2), 
      Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 15,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num), 
      sq_nonneg (sqrt 3 - sqrt 5),
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)
    ]
  have h2 : -2 + sqrt 3 + sqrt 5 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
      sq_nonneg (sqrt 3 - 1), sq_nonneg (sqrt 5 - 2), 
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
    ]
  rw [h1]
  rw [Real.sqrt_sq (by linarith [h2])]
  all_goals linarith [h2]