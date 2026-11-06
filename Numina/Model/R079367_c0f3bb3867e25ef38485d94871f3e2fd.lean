import Mathlib

theorem algebra_3809 (f : Polynomial ℝ) (hf : f = 4 * X ^ 4 + 12 * X ^ 3 - 7 * X ^ 2 - 24 * X - 9) :
    f = (X + 3) * (2 * X + 1) * (X + 1) * (2 * X - 3) := by 
  rw [hf]
  ring