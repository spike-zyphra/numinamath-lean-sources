import Mathlib

open Real

theorem inequalities_187901 (a b c : ℝ) :
    sqrt ((a + c) ^ 2 + b ^ 2) + sqrt ((a - c) ^ 2 + b ^ 2) ≥
    2 * sqrt (a ^ 2 + b ^ 2) := by
  have h1 : sqrt ((a + c) ^ 2 + b ^ 2) ≥ 0 := by positivity
  have h2 : sqrt ((a - c) ^ 2 + b ^ 2) ≥ 0 := by positivity
  have h3 : 2 * sqrt (a ^ 2 + b ^ 2) ≥ 0 := by positivity

  have h4 : (sqrt ((a + c) ^ 2 + b ^ 2) + sqrt ((a - c) ^ 2 + b ^ 2)) ^ 2 ≥ (2 * sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
    have h5 : sqrt ((a + c) ^ 2 + b ^ 2) ^ 2 = (a + c) ^ 2 + b ^ 2 := by rw [Real.sq_sqrt]; positivity
    have h6 : sqrt ((a - c) ^ 2 + b ^ 2) ^ 2 = (a - c) ^ 2 + b ^ 2 := by rw [Real.sq_sqrt]; positivity
    have h7 : sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := by rw [Real.sq_sqrt]; positivity
    have h8 : (sqrt ((a + c) ^ 2 + b ^ 2) + sqrt ((a - c) ^ 2 + b ^ 2)) ^ 2 =
        (sqrt ((a + c) ^ 2 + b ^ 2) ) ^ 2 + (sqrt ((a - c) ^ 2 + b ^ 2) ) ^ 2 + 2 * (sqrt ((a + c) ^ 2 + b ^ 2) * sqrt ((a - c) ^ 2 + b ^ 2) ) := by ring
    have h9 : (2 * sqrt (a ^ 2 + b ^ 2)) ^ 2 = 4 * (sqrt (a ^ 2 + b ^ 2) ^ 2) := by ring

    rw [h8, h5, h6, h9, h7]

    nlinarith [ sq_nonneg (sqrt ((a + c) ^ 2 + b ^ 2) - sqrt ((a - c) ^ 2 + b ^ 2)), sq_nonneg (sqrt (a ^ 2 + b ^ 2) ), 
          Real.sqrt_nonneg ((a + c) ^ 2 + b ^ 2), 
          Real.sqrt_nonneg ((a - c) ^ 2 + b ^ 2), 
          Real.sqrt_nonneg (a ^ 2 + b ^ 2), 
          mul_nonneg (Real.sqrt_nonneg ((a + c) ^ 2 + b ^ 2)) 
                      (Real.sqrt_nonneg ((a - c) ^ 2 + b ^ 2)), 
          sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + c) ^ 2 + b ^ 2 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - c) ^ 2 + b ^ 2 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) by positivity), 
          Real.sqrt_le_sqrt (show ( (a ^ 2 + b ^ 2) ) ≥ 0 by positivity ), 
          Real.sqrt_nonneg ( (a ^ 2 + b ^ 2) ), 
          mul_self_nonneg (b + c), mul_self_nonneg (b - c), 
          mul_self_nonneg (a * b), 
          mul_nonneg (Real.sqrt_nonneg ((a + c) ^ 2 + b ^ 2)) 
                      (Real.sqrt_nonneg ((a - c) ^ 2 + b ^ 2)), 
          sq_nonneg ( (a + c) * (a - c) - b ^ 2), 
          sq_nonneg (c ^ 2 - b ^ 2), 
          sq_nonneg (c * a), 
          sq_nonneg (a * b * c)
        ]

  nlinarith [ h1, h2, h3, h4 ]