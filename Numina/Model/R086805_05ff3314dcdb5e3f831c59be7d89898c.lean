import Mathlib

theorem algebra_297909 {x y z : ℝ} (h1 : x = 6 - y) (h2 : z ^ 2 = x * y - 9) : x = y := by
  rw [h1] at h2
  have h3 : (y - 3) ^ 2 + z ^ 2 = 0 := by
    nlinarith
  have h4 : (y - 3) ^ 2 = 0 := by
    linarith [sq_nonneg (y - 3), sq_nonneg z]
  have h5 : z ^ 2 = 0 := by
    linarith [sq_nonneg (y - 3), sq_nonneg z]
  have hy : y = 3 := by
    nlinarith
  have hx : x = 3 := by
    rw [hy] at h1
    linarith
  linarith [hx, hy]