import Mathlib

theorem algebra_10263 : (21 / Real.sqrt 21) = Real.sqrt 21 := by 
  have h1 : Real.sqrt 21 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  field_simp [h1]
  <;> nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]