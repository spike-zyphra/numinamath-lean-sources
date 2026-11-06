import Mathlib

theorem algebra_10248 : 1 / (1 + 1 / (Real.sqrt 3 + 1)) = Real.sqrt 3 - 1 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h2 : 1 / (Real.sqrt 3 + 1) = (Real.sqrt 3 - 1) / 2 := by
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by
      have h5 : Real.sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      linarith
    ), h1]
    <;> nlinarith [Real.sqrt_nonneg 3, h1, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
  have h3 : 1 + (Real.sqrt 3 - 1) / 2 = (Real.sqrt 3 + 1) / 2 := by
    field_simp
    <;> nlinarith [Real.sqrt_nonneg 3, h1, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
  have h4 : 1 / ((Real.sqrt 3 + 1) / 2) = 2 / (Real.sqrt 3 + 1) := by
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by
      have h5 : Real.sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      linarith
    )]
    all_goals linarith
  rw [h2, h3, h4]
  have h6 : 2 / (Real.sqrt 3 + 1) = Real.sqrt 3 - 1 := by
    have h7 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h8 : Real.sqrt 3 + 1 > 0 := by
      linarith [Real.sqrt_nonneg 3, h7]
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by linarith)]
    <;> nlinarith [h1, Real.sqrt_nonneg 3, h7]
  rw [h6]
  all_goals nlinarith [Real.sqrt_nonneg 3, h1]