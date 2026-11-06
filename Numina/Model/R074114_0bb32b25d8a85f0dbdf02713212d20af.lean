import Mathlib

theorem algebra_234710 (x : ℝ) (hx : x > 0) (h : (x + 2) * (x + 5) = x ^ 2 + 45) :
    x ^ 2 = 25 := by
  have eq1 : (x + 2) * (x + 5) = x^2 + 7 * x + 10 := by
    ring
  rw [eq1] at h
  have eq2 : 7 * x + 10 = 45 := by
    linarith
  have hx5 : x = 5 := by
    linarith
  rw [hx5]
  norm_num