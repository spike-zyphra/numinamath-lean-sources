import Mathlib

theorem algebra_114483 (r : ℝ) (hr : r > 0) (h : 10 * r = 10 * (r + 30) + r) :
    10 * r ≤ 10 * (r + 150) + r := by 
  linarith