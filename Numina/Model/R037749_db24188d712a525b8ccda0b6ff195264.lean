import Mathlib

theorem algebra_281885 {a b : ℝ} (h : a + b = 1) :
    a ^ 3 + b ^ 3 + 3 * (a ^ 3 * b + a * b ^ 3) + 6 * (a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3) = 1 := by 
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring