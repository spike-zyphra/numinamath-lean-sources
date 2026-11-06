import Mathlib

theorem algebra_2408 (x : ℝ) (hx : 0 < x) (h : (1 - 15 / 100) * x = 4250) :
    x ≥ 5000 := by
  linarith