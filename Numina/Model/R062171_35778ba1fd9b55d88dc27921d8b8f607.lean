import Mathlib

theorem algebra_153742 {x y : ℝ} (h : (x + y)^2 = (x + 1) * (y - 1)) :
    (x, y) = (-1, 1) := by
  have h1 : x^2 + y^2 + x * y + x - y + 1 = 0 := by 
    nlinarith 
  have h_eq1 : (y - 1)^2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
  have hy1 : y = 1 := by
    nlinarith [pow_two_nonneg (y - 1), pow_two_nonneg (x + 1), pow_two_nonneg (x - y)]
  rw [hy1] at h1
  have hx1 : x = -1 := by
    nlinarith 
  simp [hx1, hy1]