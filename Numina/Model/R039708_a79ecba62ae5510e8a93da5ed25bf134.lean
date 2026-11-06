import Mathlib

open Real

theorem algebra_315200 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b * (a + b) = 4) :
    2 * a + b ≥ 2 * sqrt 3 := by
  have h1 : (2 * a + b) ^ 2 ≥ 12 := by
    nlinarith [sq_nonneg (a - (b / 2 : ℝ)), sq_nonneg (a * b - 2 / 3 : ℝ), 
          sq_nonneg (a * (a + b) - 2 : ℝ), sq_nonneg (b * (a + b) - 2 : ℝ), 
          sq_nonneg (a ^ 2 - b ^ 2 : ℝ), 
          sq_nonneg (a * b : ℝ), mul_pos ha hb, sq_nonneg (a - (b / 2 : ℝ)), 
          sq_nonneg ((a + b) ^ 2 - 4 : ℝ), 
          sq_nonneg (a - (b / 2 : ℝ)), 
          sq_nonneg (a * (a + b) - b * (a + b) : ℝ), 
          sq_nonneg (a * b - (2 / 3 : ℝ)), 
          mul_pos ha (show 0 < b by linarith)
        ]
  have h3 : (2 * a + b) ≥ 0 := by nlinarith
  have h4 : (2 * a + b) ≥ 2 * Real.sqrt 3 := by
    have h5 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg ( (2 * a + b) - 2 * Real.sqrt 3 )
    ]
  linarith