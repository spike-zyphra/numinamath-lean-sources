import Mathlib

open Real

theorem inequalities_34871 (x : ℝ) (hx : x > 0) :
    x^2 + 1 / (4 * x) ≠ Real.sqrt 3 - 1 := by
  by_contra h
  have h1 : x ^ 2 + 1 / (4 * x) = Real.sqrt 3 - 1 := by
    linarith [h]
  have h5 : x ^ 2 + 1 / (4 * x) ≥ 3 / 4 := by
    have hx2_pos : x > 0 := hx
    have h6 : x ^ 2 + 1 / (4 * x) - (3 / 4) ≥ 0 := by
      have hx7 : 4 * x > 0 := by linarith
      have h8 : x ^ 2 + 1 / (4 * x) - (3 / 4) = (4 * x ^ 3 - 3 * x + 1) / (4 * x) := by
        field_simp
        ring
      rw [h8]
      have h9 : (4 * x ^ 3 - 3 * x + 1) / (4 * x) ≥ 0 := by
        apply div_nonneg
        · -- Show 4x ^ 3 - 3x + 1 ≥ 0
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x * 2 - 1), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x), sq_nonneg ((x) ^ 2 - 1 / 4), sq_nonneg ((x) - 1 / 2), sq_nonneg (x * 2 - 1)]
        · -- Show 4x ≥ 0
          nlinarith
      linarith
    linarith
  have h6 : Real.sqrt 3 - 1 < (3 / 4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3]
  have h7 : x ^ 2 + 1 / (4 * x) > Real.sqrt 3 - 1 := by
    linarith [h5, h6]
  linarith [h7, h1]