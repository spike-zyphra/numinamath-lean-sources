import Mathlib

theorem algebra_125003 {x y : ℝ} (h1 : x = y + 2) (h2 : 5 * x + 5 * y = 330) :
    x = 34 := by 
  rw [h1] at h2
  linarith