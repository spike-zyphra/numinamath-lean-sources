import Mathlib

theorem inequalities_289212 : Real.sqrt 2005 + Real.sqrt 2007 < 2 * Real.sqrt 2006 := by
  have h1 : 0 < Real.sqrt 2005 := by positivity
  have h2 : 0 < Real.sqrt 2007 := by positivity
  have h3 : 0 < Real.sqrt 2006 := by positivity

  have h4 : (Real.sqrt 2005 + Real.sqrt 2007) ^ 2 < (2 * Real.sqrt 2006) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2005 - Real.sqrt 2007),
      sq_nonneg (Real.sqrt 2006 - 1),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2005 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2007 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2006 : ℝ) by norm_num),
      mul_nonneg (Real.sqrt_nonneg 2005) (Real.sqrt_nonneg 2007),
      mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2006),
      Real.sqrt_nonneg 2005, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2006,
      sq_nonneg (Real.sqrt 2005 ^ 2 - 2005),
      sq_nonneg (Real.sqrt 2007 ^ 2 - 2007),
      sq_nonneg (Real.sqrt 2006 ^ 2 - 2006),
      mul_pos (show (0 : ℝ) < (2005 : ℝ) by norm_num) (show (0 : ℝ) < (2007 : ℝ) by norm_num),
      mul_pos (show (0 : ℝ) < (2005 : ℝ) by norm_num) (show (0 : ℝ) < (2006 : ℝ) by norm_num),
      mul_pos (show (0 : ℝ) < (2007 : ℝ) by norm_num) (show (0 : ℝ) < (2006 : ℝ) by norm_num)]

  have h6 : 0 < Real.sqrt 2005 + Real.sqrt 2007 := by positivity
  have h7 : 0 < 2 * Real.sqrt 2006 := by positivity
  nlinarith [Real.sqrt_nonneg 2005, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2006, h4, mul_nonneg (Real.sqrt_nonneg 2005) (Real.sqrt_nonneg 2007)]