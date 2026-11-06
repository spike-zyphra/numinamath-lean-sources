import Mathlib

theorem algebra_185022 : (1 / (Real.sqrt 7 - Real.sqrt 6)) = (3 / (Real.sqrt 6 - Real.sqrt 3)) + (4 / (Real.sqrt 7 + Real.sqrt 3)) := by

  have eq1 : 1 / (Real.sqrt 7 - Real.sqrt 6) = Real.sqrt 7 + Real.sqrt 6 := by
    field_simp [(show Real.sqrt 7 - Real.sqrt 6 ≠ 0 by
      have h : Real.sqrt 7 > Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith [h, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7]
    )]
    <;> nlinarith [Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 7, Real.sqrt_nonneg 6]

  have eq2 : 3 / (Real.sqrt 6 - Real.sqrt 3) = Real.sqrt 6 + Real.sqrt 3 := by
    field_simp [(show Real.sqrt 6 - Real.sqrt 3 ≠ 0 by
      have h : Real.sqrt 6 > Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith [h, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6]
    )]
    <;> nlinarith [Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 3]

  have eq3 : 4 / (Real.sqrt 7 + Real.sqrt 3) = Real.sqrt 7 - Real.sqrt 3 := by
    field_simp [(show Real.sqrt 7 + Real.sqrt 3 ≠ 0 by
      positivity
    )]
    <;> nlinarith [Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 7, Real.sqrt_nonneg 3]

  rw [eq1, eq2, eq3]
  linarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 6, Real.sqrt_nonneg 3]