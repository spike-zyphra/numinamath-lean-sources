import Mathlib

theorem algebra_189052 : (1 / (Real.sqrt 2 - 1) - 1 / (Real.sqrt 2 + 1) +
    1 / (Real.sqrt 3 - 1) - 1 / (Real.sqrt 3 + 1)) = 3 := by
  have h1 : Real.sqrt 2 > 0 := by
    positivity
  have h2 : Real.sqrt 3 > 0 := by
    positivity
  have h3 : Real.sqrt 2 > 1 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h4 : Real.sqrt 3 > 1 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h5 : (Real.sqrt 2 - 1) ≠ 0 := by 
    nlinarith [show Real.sqrt 2 > 1 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]]
  have eq1 : 1 / (Real.sqrt 2 - 1) = Real.sqrt 2 + 1 := by
    have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    field_simp [h5]
    <;> nlinarith [h6, show Real.sqrt 2 > 0 by positivity]
  have eq2 : 1 / (Real.sqrt 2 + 1) = Real.sqrt 2 - 1 := by 
    have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    field_simp [(show Real.sqrt 2 + 1 ≠ 0 by nlinarith [show Real.sqrt 2 > 0 by positivity])]
    <;> nlinarith [h6, show Real.sqrt 2 > 0 by positivity]
  have eq3 : 1 / (Real.sqrt 3 - 1) = (Real.sqrt 3 + 1) / 2 := by
    have h7 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    field_simp [(show Real.sqrt 3 - 1 ≠ 0 by nlinarith [show Real.sqrt 3 > 1 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]]) ]
    <;> nlinarith [h7, show Real.sqrt 3 > 0 by positivity]
  have eq4 : 1 / (Real.sqrt 3 + 1) = (Real.sqrt 3 - 1) / 2 := by 
    have h7 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by nlinarith [show Real.sqrt 3 > 0 by positivity])]
    <;> nlinarith [h7, show Real.sqrt 3 > 0 by positivity]
  rw [eq1, eq2, eq3, eq4]
  have h8 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h9 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 2 + 1), sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1)]