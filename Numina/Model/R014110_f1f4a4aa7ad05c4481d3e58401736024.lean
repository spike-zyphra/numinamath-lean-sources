import Mathlib

theorem algebra_150236 (x y : ℝ) (h1 : 3 * x ≥ 2 * y + 16) (h2 : x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4 + 25 - 26 * x ^ 2 - 26 * y ^ 2 = 72 * x * y) :
    (x, y) = (6, 1) := by
  have h3 : (x - 6) ^ 2 + (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2 - 1 + 2), sq_nonneg (2 * x * y - 6), sq_nonneg (x - 6), sq_nonneg (y - 1),
              sq_nonneg (x + y - 7), sq_nonneg (x - y - 5)]
  have hx1 : (x - 6) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 6), sq_nonneg (y - 1), h3]
  have hx2 : x - 6 = 0 := by
    nlinarith
  have hx3 : x = 6 := by
    linarith
  have hy1 : (y - 1) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 6), sq_nonneg (y - 1), h3]
  have hy2 : y - 1 = 0 := by
    nlinarith
  have hy3 : y = 1 := by
    linarith
  simp [hx3, hy3]