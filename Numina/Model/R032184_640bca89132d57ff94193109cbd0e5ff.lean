import Mathlib

theorem algebra_21331 (d : ℝ) (h : d = 12000) (v1 v2 : ℝ) (h1 : v1 = 48) (h2 : v2 = 15) :
    d / v2 - d / v1 = 550 := by
  rw [h, h1, h2]
  norm_num