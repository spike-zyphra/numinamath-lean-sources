import Mathlib

theorem algebra_175129 (a b c d m : ℝ) (ha : a * m + k = b) (hc : c * m + k = d) :
    Real.sqrt ((a - c)^2 * (1 + m^2)) = |a - c| * Real.sqrt (1 + m^2) := by
  have h1 : Real.sqrt ((a - c) ^ 2 * (1 + m ^ 2)) = Real.sqrt ((a - c) ^ 2) * Real.sqrt (1 + m ^ 2) := by
    rw [Real.sqrt_mul (by positivity)]
  have h2 : Real.sqrt ((a - c) ^ 2) = |a - c| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h2] at h1
  linarith [h1]