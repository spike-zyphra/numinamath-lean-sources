import Mathlib

theorem algebra_154123 {a b c : ℝ} (h : a + b + c = 1) :
    a ^ 4 + b ^ 4 + c ^ 4 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / 2 - (a ^ 2 + b ^ 2 + c ^ 2) + (4 / 3) * (a ^ 3 + b ^ 3 + c ^ 3) + 1 / 6 := by 
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  ring