import Mathlib

theorem algebra_129692 {x y : ℝ} (h₁ : x^3 = 3 * y^2 * x + 5 - Real.sqrt 7) (h₂ : y^3 = 3 * x^2 * y + 5 + Real.sqrt 7) :
    x^2 + y^2 = 4 := by
  have h3 : (x + y) ^ 3 - 6 * (x * y) * (x + y) - 10 = 0 := by
    nlinarith [h₁, h₂, Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  have h4 : (y - x) * ((x + y) ^ 2 + 2 * (x * y)) = 2 * Real.sqrt 7 := by
    nlinarith [h₁, h₂, Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (x ^2 - y ^2)]