import Mathlib

theorem algebra_126354 (xiao_ming xiao_hong : ℝ) (h : xiao_ming > 0) (h' : xiao_hong > 0)
    (h1 : xiao_ming + xiao_hong = 600 / 50) (h2 : xiao_hong = xiao_ming - 2) :
    xiao_ming = 7 := by 
  rw [h2] at h1
  linarith