import Mathlib

theorem algebra_1624 : (-√2 + √3 + √5) * (√2 - √3 + √5) * (√2 + √3 - √5) * (√2 + √3 + √5) = 24 := by
  have h1 : (√2 : ℝ) ^ 2 = 2 := by norm_num [Real.sq_sqrt]
  have h2 : (√3 : ℝ) ^ 2 = 3 := by norm_num [Real.sq_sqrt]
  have h3 : (√5 : ℝ) ^ 2 = 5 := by norm_num [Real.sq_sqrt]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
    sq_nonneg (√2 - √3), sq_nonneg (√2 - √5), sq_nonneg (√3 - √5),
    sq_nonneg (√2 + √3 - √5), sq_nonneg (√2 + √3 + √5)
  ]