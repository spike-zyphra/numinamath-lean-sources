import Mathlib

theorem inequalities_155249 (a b x y : ℝ) :
    |a * x ^ 2 + 2 * b * x * y - a * y ^ 2| ≤ √(a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  have h1 : (a * x ^ 2 + 2 * b * x * y - a * y ^ 2 : ℝ) ^ 2 ≤ (a ^ 2 + b ^ 2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (2 * a * x * y - b * (x ^ 2 - y ^ 2)), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (a * x - b * y), sq_nonneg (a * y - b * x), sq_nonneg (a * (x ^ 2 - y ^ 2) + 2 * b * x * y), sq_nonneg ((x ^ 2 + y ^ 2) * b - a * (x ^ 2 - y ^ 2)), sq_nonneg (2 * x * y), sq_nonneg ((a * x - b * y) * (x - y)), sq_nonneg ((a * y + b * x) * (x + y))]
  have h2 : |a * x ^ 2 + 2 * b * x * y - a * y ^ 2| ≤ Real.sqrt ( (a ^ 2 + b ^ 2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 ) := by
    have h3 : Real.sqrt ( (a * x ^ 2 + 2 * b * x * y - a * y ^ 2 : ℝ) ^ 2 ) = |a * x ^ 2 + 2 * b * x * y - a * y ^ 2| := by
      rw [Real.sqrt_sq_eq_abs]
    have h4 : Real.sqrt ( (a * x ^ 2 + 2 * b * x * y - a * y ^ 2 : ℝ) ^ 2 ) ≤ Real.sqrt ( (a ^ 2 + b ^ 2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith [h1]
    linarith [h3, h4]
  have h3 : Real.sqrt ( (a ^ 2 + b ^ 2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 ) = Real.sqrt (a^2 + b^2) * (x^2 + y^2) := by
    have h4 : Real.sqrt ( (a ^ 2 + b ^ 2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 ) = Real.sqrt (a^2 + b^2) * Real.sqrt ( (x^2 + y^2) ^2 ) := by
      rw [← Real.sqrt_mul (by positivity)]
    have h5 : Real.sqrt ( (x^2 + y^2 : ℝ) ^ 2 ) = x ^ 2 + y ^ 2 := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 by positivity)]
    rw [h4, h5]
  linarith [h2, h3]