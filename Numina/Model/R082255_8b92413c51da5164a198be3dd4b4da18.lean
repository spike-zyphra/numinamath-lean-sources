import Mathlib

theorem algebra_304469 {x y z : ℝ} (h1 : x + y = 6) (h2 : z^2 = x * y - 9) : x = y := by
  have h3 : y = 6 - x := by linarith
  rw [h3] at h2
  have h4 : (x - 3) ^ 2 + z ^ 2 = 0 := by
    nlinarith
  have h5 : (x - 3) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 3), sq_nonneg z]
  have h6 : x - 3 = 0 := by
    rw [sq_eq_zero_iff] at h5
    exact h5
  have hx : x = 3 := by linarith
  have hy : y = 3 := by linarith [h1, hx]
  linarith [hx, hy]