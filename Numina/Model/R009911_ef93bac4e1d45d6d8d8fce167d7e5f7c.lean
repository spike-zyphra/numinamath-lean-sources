import Mathlib

theorem algebra_20065 {a b : ℝ} (h : a < b) : |a - b| + a + b = 2 * b := by
  have h1 : a - b < 0 := by linarith
  rw [abs_of_neg h1]
  linarith