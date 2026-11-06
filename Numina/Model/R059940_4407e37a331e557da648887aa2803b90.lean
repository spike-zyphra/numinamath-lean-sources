import Mathlib

theorem algebra_183116 (x y : ℝ) (h : 4*x+8*y=1000) (h' : x=y+214) :
    8*y/24=4 := by
  have eq1 : x = y + 214 := h'
  rw [eq1] at h 
  have hy : y = 12 := by
    linarith
  rw [hy]
  norm_num