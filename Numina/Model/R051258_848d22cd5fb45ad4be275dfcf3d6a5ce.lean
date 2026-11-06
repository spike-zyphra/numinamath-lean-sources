import Mathlib

theorem algebra_173388 (u v : ℝ) (hu : u > 0) (hv : v = 1) (h : u * v = 3.5) :
    u = 3.5 := by
  rw [hv] at h
  linarith