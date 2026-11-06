import Mathlib

theorem algebra_9428 {a : ℝ} (h : (-2)^2 - a * (-2) - 3 * a = 0) :
    (6)^2 - a * 6 - 3 * a = 0 := by
  have ha : a = 4 := by
    linarith 
  rw [ha]
  norm_num