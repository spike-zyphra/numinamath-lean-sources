import Mathlib

open Real Set

theorem algebra_303675 (x : ℝ) :
    sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 13 := by
  have h1 : sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 13 := by
    have h2 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 ≥ 13 ^ 2 := by
      have h3 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 = 
          (sqrt (x ^ 2 + 4)) ^ 2 + (sqrt ((12 - x) ^ 2 + 9)) ^ 2 + 
          2 * (sqrt (x ^ 2 + 4) * sqrt ((12 - x) ^ 2 + 9)) := by 
        ring
      rw [h3]
      have h4 : (sqrt (x ^ 2 + 4)) ^ 2 = x ^ 2 + 4 := by 
        rw [Real.sq_sqrt]
        positivity
      have h5 : (sqrt ((12 - x) ^ 2 + 9)) ^ 2 = (12 - x) ^ 2 + 9 := by 
        rw [Real.sq_sqrt]
        positivity
      rw [h4, h5]
      nlinarith [sq_nonneg (sqrt (x ^ 2 + 4) - 5.2), sq_nonneg (sqrt ((12 - x) ^ 2 + 9) - 7.8), 
          Real.sqrt_nonneg (x ^ 2 + 4), Real.sqrt_nonneg ((12 - x) ^ 2 + 9), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4)) (Real.sqrt_nonneg ((12 - x) ^ 2 + 9)), 
          sq_nonneg (x - 4.8), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 4 by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (12 - x) ^ 2 + 9 by nlinarith), 
          Real.sqrt_nonneg (x ^ 2 + 4), 
          Real.sqrt_nonneg ((12 - x) ^ 2 + 9)
        ]
    have h6 : sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 0 := by positivity
    have h7 : (13 : ℝ) ≥ 0 := by norm_num
    nlinarith [sq_nonneg (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) - 13), 
        Real.sqrt_nonneg (x ^ 2 + 4), 
        Real.sqrt_nonneg ((12 - x) ^ 2 + 9)
      ]
  linarith [h1]