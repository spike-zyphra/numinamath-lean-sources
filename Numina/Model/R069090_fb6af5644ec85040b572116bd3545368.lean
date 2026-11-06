import Mathlib

theorem algebra_1123 {a b c d: ℝ} (hP : b = a + 5) (hQ : d = c + 5) : a * d + b * c - a * c - b * d = -25 := by 
  rw [hP, hQ]
  ring