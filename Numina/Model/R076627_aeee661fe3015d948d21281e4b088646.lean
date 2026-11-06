import Mathlib

theorem algebra_309007 : ((1 + Real.sqrt 2013 * (Real.sqrt 2012 - Real.sqrt 2011)) / (Real.sqrt 2011 + Real.sqrt 2012 + Real.sqrt 2013) + Real.sqrt 2011 = Real.sqrt 2012) := by
  have h1 : Real.sqrt 2011 ≥ 0 := Real.sqrt_nonneg 2011
  have h2 : Real.sqrt 2012 ≥ 0 := Real.sqrt_nonneg 2012
  have h3 : Real.sqrt 2013 ≥ 0 := Real.sqrt_nonneg 2013
  have h4 : Real.sqrt 2011 + Real.sqrt 2012 + Real.sqrt 2013 > 0 := by
    positivity
  field_simp [h4]
  nlinarith [Real.sqrt_nonneg 2011, Real.sqrt_nonneg 2012, Real.sqrt_nonneg 2013,
          Real.sq_sqrt (show (0 : ℝ) ≤ (2011 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2012 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2013 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2011) (Real.sqrt_nonneg 2012),
          mul_nonneg (Real.sqrt_nonneg 2011) (Real.sqrt_nonneg 2013),
          mul_nonneg (Real.sqrt_nonneg 2012) (Real.sqrt_nonneg 2013),
          pow_two_nonneg (Real.sqrt 2013 - Real.sqrt 2012),
          pow_two_nonneg (Real.sqrt 2012 - Real.sqrt 2011),
          pow_two_nonneg (Real.sqrt 2013 - Real.sqrt 2011)
        ]