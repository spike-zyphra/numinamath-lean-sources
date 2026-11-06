import Mathlib

theorem algebra_307797 : (2 * Real.sqrt 6) / (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) =
    Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5 := by
  have h1 : Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 ≠ 0 := by
    have h2 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h3 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h4 : Real.sqrt 5 > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    linarith

  have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    calc
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]

  have eq1 : (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) * (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5) = 2 * Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_pos (show Real.sqrt 2 > 0 by positivity) (show Real.sqrt 3 > 0 by positivity)]
  
  field_simp [h1]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, eq1, h2, mul_pos (show Real.sqrt 2 > 0 by positivity) (show Real.sqrt 3 > 0 by positivity)]