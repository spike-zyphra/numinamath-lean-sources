import Mathlib

theorem inequalities_178331 (a b : ℝ) (h : a + b = 1) :
    (a + 1)^2 + (b + 1)^2 ≥ 9 / 2 := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  nlinarith [sq_nonneg (a - 1 / 2)]