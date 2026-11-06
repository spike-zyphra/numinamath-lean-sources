import Mathlib

theorem algebra_195135 {x b : ℝ} (h : x^3 + 6 * x^2 + 12 * x + 17 = (x + 2)^3 + b) :
    b = 9 := by
  have eq1 : (x + 2)^3 = x^3 + 6 * x^2 + 12 * x + 8 := by
    ring
  rw [eq1] at h
  linarith