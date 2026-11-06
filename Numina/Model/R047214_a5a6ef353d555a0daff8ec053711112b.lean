import Mathlib

theorem algebra_106191 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0) :
    5 * x ^ 2 + 5 * y ^ 2 + 5 * z ^ 2 + 6 * x * y - 8 * x * z - 8 * y * z > 0 := by
  have h2 : 5 * x ^ 2 + 5 * y ^ 2 + 5 * z ^ 2 + 6 * x * y - 8 * x * z - 8 * y * z ≥ 0 := by
    nlinarith [sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y + z), sq_nonneg (x - y - z), sq_nonneg (x + y - 2 * z), sq_nonneg (2 * x + 2 * y - z)]
  by_contra h3
  have h4 : 5 * x ^ 2 + 5 * y ^ 2 + 5 * z ^ 2 + 6 * x * y - 8 * x * z - 8 * y * z ≤ (0 : ℝ) := by linarith
  have h5 : 5 * x ^ 2 + 5 * y ^ 2 + 5 * z ^ 2 + 6 * x * y - 8 * x * z - 8 * y * z = 0 := by linarith
  have h6 : x^2 + y^2 + z^2 = 0 := by
    nlinarith [sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y + z), sq_nonneg (x - y - z), sq_nonneg (x + y - 2 * z), sq_nonneg (2 * x + 2 * y - z)]
  contradiction