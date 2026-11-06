import Mathlib

theorem algebra_3010 : (Real.sqrt 3755 + Real.sqrt 3752) * (-Real.sqrt 3755 - Real.sqrt 3752) * (Real.sqrt 3755 - Real.sqrt 3752) * (Real.sqrt 3752 - Real.sqrt 3755) = 9 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3755 : ℝ) by norm_num),
           Real.sq_sqrt (show (0 : ℝ) ≤ (3752 : ℝ) by norm_num),
           sq_nonneg (Real.sqrt 3755 - Real.sqrt 3752),
           sq_nonneg (Real.sqrt 3755 + Real.sqrt 3752),
           sq_nonneg (Real.sqrt 3752 - Real.sqrt 3755),
           sq_nonneg (Real.sqrt 3752 + Real.sqrt 3755),
           Real.sqrt_nonneg 3755, Real.sqrt_nonneg 3752,
           mul_nonneg (Real.sqrt_nonneg 3755) (Real.sqrt_nonneg 3752),
           mul_self_nonneg (Real.sqrt 3755 - Real.sqrt 3752),
           mul_self_nonneg (Real.sqrt 3752 - Real.sqrt 3755)
           ]