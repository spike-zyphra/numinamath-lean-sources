import Mathlib

theorem algebra_259437 {x : ℝ} (hx : x ≠ 0) (h : 20 * x + 40 * x + 60 * x + 80 * x + 100 * x + 120 * x + 140 * x = 20 * 20 + 40 * 20 + 60 * 20 + 80 * 20 + 100 * 20 + 120 * 20 + 140 * 20) :
    x = 20 := by 
  linarith