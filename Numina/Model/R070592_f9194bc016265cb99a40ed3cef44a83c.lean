import Mathlib

theorem algebra_314853 : (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) * (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) = 104 := by 
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7,
            Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num),
            Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num),
            Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num),
            sq_nonneg (Real.sqrt 5 - Real.sqrt 6),
            sq_nonneg (Real.sqrt 5 - Real.sqrt 7),
            sq_nonneg (Real.sqrt 6 - Real.sqrt 7),
            mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6),
            mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7),
            mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 7),
            sq_nonneg (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7),
            sq_nonneg (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7),
            sq_nonneg (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7)]