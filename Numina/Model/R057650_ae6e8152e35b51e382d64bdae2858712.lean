import Mathlib

open Real

theorem algebra_13648 : (1 / (1 + sqrt 2)) * (1 / (1 - sqrt 2)) = -1 := by
  have h1 : (1 + sqrt 2) ≠ 0 := by
    have h2 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    have h3 : (1 + sqrt 2) > 0 := by linarith
    linarith
  have h4 : (1 - sqrt 2) ≠ 0 := by
    have h5 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    have h6 : sqrt 2 > 1 := by
      have h7 : sqrt 2 > sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h8 : sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith [h7, h8]
    have h9 : (1 - sqrt 2) < 0 := by linarith
    intro h
    linarith
  field_simp [h1, h4]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]