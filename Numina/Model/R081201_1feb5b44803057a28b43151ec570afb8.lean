import Mathlib

theorem algebra_283683 {x : ℝ} (h : x^2 + x - 1 = 0) : x^4 - 3 * x^2 + 3 = 2 := by
  have h1 : x^2 = 1 - x := by 
    linarith
  have h2 : x^4 = (2 - 3 * x) := by 
    calc
      x^4 = (x^2)^2 := by ring
      _ = (1 - x)^2 := by rw [h1]
      _ = 1 - 2 * x + x^2 := by ring
      _ = 1 - 2 * x + (1 - x) := by rw [h1]
      _ = (2 - 3 * x) := by ring
  rw [h2, h1]
  ring