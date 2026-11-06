import Mathlib

theorem algebra_274420 {x : ℤ} (h : x + (x + 1) + (x + 2) = 27) :
    x * (x + 1) * (x + 2) = 720 := by
  have hx : x = 8 := by 
    linarith 
  rw [hx]
  norm_num