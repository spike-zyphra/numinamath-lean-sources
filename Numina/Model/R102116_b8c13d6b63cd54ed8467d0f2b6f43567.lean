import Mathlib

theorem algebra_298232 {x y : ℝ} (h : x^2 + 12 * x * y + 52 * y^2 - 8 * y + 1 = 0) : x^2 - y^2 = 35 / 16 := by
  have h1 : (x + 6 * y)^2 + (4 * y - 1)^2 = 0 := by 
    nlinarith [sq_nonneg (x + 6 * y), sq_nonneg (4 * y - 1)]
  have h2 : (x + 6 * y)^2 = 0 := by 
    linarith [sq_nonneg (x + 6 * y), sq_nonneg (4 * y - 1)]
  have h3 : (4 * y - 1)^2 = 0 := by 
    linarith [sq_nonneg (x + 6 * y), sq_nonneg (4 * y - 1)]
  have hy : y = 1 / 4 := by
    nlinarith
  have hx : x = -3 / 2 := by
    nlinarith [h2, hy]
  rw [hx, hy]
  norm_num