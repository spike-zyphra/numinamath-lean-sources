import Mathlib

theorem algebra_105316 {a b : ℤ} (h : a + b = 4) : a^3 + 12 * a * b + b^3 = 64 := by 
  have h1 : b = 4 - a := by linarith 
  rw [h1]
  ring