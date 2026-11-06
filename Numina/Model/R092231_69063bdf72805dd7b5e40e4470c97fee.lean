import Mathlib

theorem algebra_184032 (x : ℝ) (hx : x = 600) (h : (1 - 98 / 100) * x = (1 - 96 / 100) * y)
    (hy : 0 < y) : y = 300 := by 
  rw [hx] at h
  have h_eq : (1 - 98 / 100 : ℝ) * (600 : ℝ) = (1 - 96 / 100 : ℝ) * y := h
  norm_num at h_eq 
  linarith