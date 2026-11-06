import Mathlib

theorem algebra_6836 {x y : ℝ} (h1 : x - y = 6) (h2 : x^2 + y^2 = 40) :
    2*x^3 + 3*x^2*y - 3*x*y^2 - 2*y^3 = 540 := by
  have h3 : x * y = 2 := by
    have h : (x - y) ^ 2 = 36 := by
      rw [h1]
      norm_num
    have h4 : (x - y) ^ 2 = x^2 + y^2 - 2 * (x * y) := by
      ring
    rw [h4] at h
    rw [h2] at h
    linarith
  have eq1 : 2*x^3 + 3*x^2*y - 3*x*y^2 - 2*y^3 = (x - y) * (2 * (x^2 + y^2) + 5 * (x * y)) := by
    ring
  rw [eq1, h1, h2, h3]
  all_goals norm_num