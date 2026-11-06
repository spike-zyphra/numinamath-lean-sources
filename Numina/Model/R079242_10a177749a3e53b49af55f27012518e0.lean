import Mathlib

theorem algebra_228467 {x : ℝ} (hx : x ≠ 0) (h : (1 / 3) * (1 + 10 / 100) + (1 / 2) * (1 - 15 / 100) + (1 - 1 / 3 - 1 / 2) * (1 + x / 100) = 1) :
    x = 25 := by 
  linarith