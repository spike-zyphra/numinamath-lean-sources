import Mathlib

theorem algebra_308550 : (Real.sqrt 30 + Real.sqrt 21 - 3) * (Real.sqrt 3 + Real.sqrt 10 - Real.sqrt 7) = 6 * Real.sqrt 7 := by 
  have h1 : Real.sqrt 30 = Real.sqrt 3 * Real.sqrt 10 := by
    calc 
      Real.sqrt 30 = Real.sqrt (3 * 10) := by norm_num
      _ = Real.sqrt 3 * Real.sqrt 10 := by rw [Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by 
    calc 
      Real.sqrt 21 = Real.sqrt (3 * 7) := by norm_num
      _ = Real.sqrt 3 * Real.sqrt 7 := by rw [Real.sqrt_mul (by norm_num)]
  rw [h1, h4]
  have h5 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have h6 : Real.sqrt 10 ^ 2 = (10 : ℝ) := Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)
  have h7 : Real.sqrt 7 ^ 2 = (7 : ℝ) := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
  have h8 : Real.sqrt 3 ≥ 0 := by positivity
  have h9 : Real.sqrt 10 ≥ 0 := by positivity
  have h10 : Real.sqrt 7 ≥ 0 := by positivity
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 10, Real.sqrt_nonneg 7, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 10),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 7),
          mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg 7)
]