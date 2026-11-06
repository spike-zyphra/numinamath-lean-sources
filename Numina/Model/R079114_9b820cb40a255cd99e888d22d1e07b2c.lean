import Mathlib

theorem algebra_306204 {x y : ℝ} (h1 : x * y + x + y + 7 = 0) (h2 : 3 * x + 3 * y = 9 + 2 * x * y) :
    x^2 * y + x * y^2 = 6 := by 
  have h3 : x + y = -7 - x * y := by
    nlinarith
  have h4 : 3 * (x + y) - 2 * (x * y) = 9 := by
    nlinarith
  rw [h3] at h4
  have h5 : x * y = -6 := by
    nlinarith
  have h6 : x + y = -1 := by
    nlinarith [h3, h5]
  have h7 : x^2 * y + x * y^2 = (x * y) * (x + y) := by
    ring
  rw [h7, h5, h6]
  norm_num