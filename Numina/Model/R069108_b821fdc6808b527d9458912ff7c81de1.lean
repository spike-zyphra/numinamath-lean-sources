import Mathlib

theorem algebra_1362 {x : ℝ} (hx : x = 2 * Real.sqrt 2 + 1) :
    (x^2 - 2 * x - 9) / (x^3 - 11 * x - 15) = 2 := by
  have h1 : x^2 - 2*x - 9 = -2 := by
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h2 : x^3 - 11*x - 15 = -1 := by
    rw [hx]
    have h1 : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pow (Real.sqrt 2) (Real.sqrt 2) 2, pow_three (Real.sqrt 2)]
  have h3 : x^3 - 11 * x - 15 ≠ 0 := by
    linarith [h2]
  field_simp [h3]
  nlinarith [h1, h2]