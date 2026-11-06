import Mathlib

theorem algebra_16456 (x : ℝ) (hx : x > 0) (h : 2 * (40 + 10) = 4 * x) :
    x ^ 2 - (40 * 10) = 225 := by 
  have hx25 : x = 25 := by
    linarith
  rw [hx25]
  norm_num