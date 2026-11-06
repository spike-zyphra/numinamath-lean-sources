import Mathlib

theorem algebra_10202 : (1 / (Real.sqrt 2 - 1)) = (Real.sqrt 2 + 1) := by
  have h1 : Real.sqrt 2 > 1 := by
    have h2 : Real.sqrt 2 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h3 : Real.sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith [h2, h3]
  have h2 : Real.sqrt 2 - 1 ≠ 0 := by
    have h3 : Real.sqrt 2 > 1 := h1
    linarith
  field_simp [h2]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]