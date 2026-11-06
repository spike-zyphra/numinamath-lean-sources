import Mathlib

theorem algebra_13128 (t : ℝ) (ht : t > 5 / 3) (h : (t + 1) * (3 * t - 3) = (3 * t - 5) * (t + 2) + 2) :
    t = 5 := by
  have eq1 : (t + 1) * (3 * t - 3) = 3 * t^2 - 3 := by
    ring
  have eq2 : (3 * t - 5) * (t + 2) + 2 = 3 * t^2 + t - 8 := by
    ring
  rw [eq1, eq2] at h
  linarith