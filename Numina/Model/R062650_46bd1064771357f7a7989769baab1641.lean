import Mathlib

theorem algebra_13969 (x a : ℝ) (h : x = a + 7) : x - a + 3 = 10 := by
  rw [h]
  linarith