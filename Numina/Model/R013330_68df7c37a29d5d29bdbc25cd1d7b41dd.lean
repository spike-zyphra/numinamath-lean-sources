import Mathlib

theorem algebra_147015 {x y : ℝ} (h1 : 2 * x + y + 8 ≤ 0) (h2 : x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4 + 9 - 10 * x ^ 2 - 10 * y ^ 2 = 8 * x * y) :
    (x, y) = (-3, -2) := by
  have h3 : (x + 3) ^ 2 + (y + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 + y^2 - 9), sq_nonneg (x + 3), sq_nonneg (y + 2), 
      sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y + 6)]
  have hx1 : x + 3 = 0 := by
    nlinarith [h3, sq_nonneg (x + 3), sq_nonneg (y + 2)]
  have hy1 : y + 2 = 0 := by
    nlinarith [h3, sq_nonneg (x + 3), sq_nonneg (y + 2)]
  have hx2 : x = -3 := by
    linarith [hx1]
  have hy2 : y = -2 := by
    linarith [hy1]
  simp [Prod.ext_iff, hx2, hy2]