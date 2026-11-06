import Mathlib

theorem algebra_167493 (d t : ℝ) (ht : t = 1.2) (h : d / 60 = t + 20 / 60) (h' : d / 90 = t - 20 / 90) :
    d = 180 := by 
  rw [ht] at h h'
  linarith