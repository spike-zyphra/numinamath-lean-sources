import Mathlib

open Real

theorem inequalities_251587 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    a * x + b * y ≤ sqrt (a^2 + b^2) * sqrt (x^2 + y^2) := by
  have h1 : 0 ≤ a * x + b * y := by
    nlinarith
  have h2 : (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (a * y - b * x)]
  have h3 : sqrt ((a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2)) = sqrt (a ^ 2 + b ^ 2) * sqrt (x ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
  have h5 : (a * x + b * y : ℝ) ≤ sqrt ((a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2)) := by
    have h6 : sqrt ((a * x + b * y) ^ 2) ≤ sqrt ((a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2)) := by
      apply Real.sqrt_le_sqrt
      linarith [h2]
    have h7 : sqrt ((a * x + b * y) ^ 2) = (a * x + b * y) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg]
      linarith [h1]
    nlinarith [h7, h6]
  linarith [h5, h3]