import Mathlib

theorem algebra_22527 : (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) *
    (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) = 104 := by 
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7,
          Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num),
          Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
          Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num),
          sq_nonneg (Real.sqrt 5 - Real.sqrt 6),
          sq_nonneg (Real.sqrt 5 - Real.sqrt 7),
          sq_nonneg (Real.sqrt 6 - Real.sqrt 7),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7),
          mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 7)
        ]