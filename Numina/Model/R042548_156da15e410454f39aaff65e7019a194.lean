import Mathlib

theorem inequalities_134485 (a b x y : ℝ)
    (h₀ : x^2 + y^2 ≤ 1) (h₁ : a^2 + b^2 ≤ 2) :
    |b * (x^2 - y^2) + 2 * a * x * y| ≤ Real.sqrt 2 := by
  have h5 : -Real.sqrt 2 ≤ b * (x^2 - y^2) + 2 * a * x * y := by
    have h912 : (b * (x^2 - y^2) + 2 * a * x * y) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg (a * (x^2 - y^2) - 2 * b * x * y), sq_nonneg (a * y - b * x), sq_nonneg (a * x + b * y), sq_nonneg (a^2 + b^2 - 2), sq_nonneg ((x^2 - y^2)^2 + 4 * x^2 * y^2 - 1), sq_nonneg (x^2 + y^2 - 1)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h6 : b * (x^2 - y^2) + 2 * a * x * y ≤ Real.sqrt 2 := by
    have h912 : (b * (x^2 - y^2) + 2 * a * x * y) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg (a * (x^2 - y^2) - 2 * b * x * y), sq_nonneg (a * y - b * x), sq_nonneg (a * x + b * y), sq_nonneg (a^2 + b^2 - 2), sq_nonneg ((x^2 - y^2)^2 + 4 * x^2 * y^2 - 1), sq_nonneg (x^2 + y^2 - 1)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  apply abs_le.mpr
  constructor <;> linarith