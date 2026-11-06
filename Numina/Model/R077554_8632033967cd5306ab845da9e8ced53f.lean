import Mathlib

theorem algebra_190947 (d : ℝ) (h : d = 300) (v1 v2 : ℝ)
    (h1 : v1 = 12 / 10) (h2 : v2 = 10 / 12) :
    (2 * 60 + 30) * v1 + (2 * 60 + 30) * v2 - d = 5 := by 
  rw [h, h1, h2]
  norm_num