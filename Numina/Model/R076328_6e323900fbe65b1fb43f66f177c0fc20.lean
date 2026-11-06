import Mathlib

theorem algebra_21783 : (33 / Real.sqrt 33 : ℝ) = Real.sqrt 33 := by 
  have h1 : Real.sqrt 33 > 0 := by
    positivity
  have h2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)
  field_simp [h1, h2]
  <;> nlinarith [Real.sqrt_nonneg 33, h2]