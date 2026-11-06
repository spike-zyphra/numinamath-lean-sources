import Mathlib

theorem algebra_2609 {a b : ℤ} (h : a - b = 3) : a ^ 3 - b ^ 3 - 9 * a * b = 27 := by
  have ha : a = b + 3 := by 
    linarith
  rw [ha]
  ring