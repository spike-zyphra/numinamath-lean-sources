import Mathlib

theorem algebra_2432 {a b : ℝ} (h : a < b) : (a - b) * abs (a - b) = -(a - b)^2 := by
  have h1 : a - b < 0 := by linarith
  rw [abs_of_neg h1]
  ring