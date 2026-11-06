import Mathlib

theorem algebra_280890 (x y : ℝ) (hx : x = 4) (h : 3 * x + 2 * y = 30) : y = 9 := by 
  rw [hx] at h
  linarith