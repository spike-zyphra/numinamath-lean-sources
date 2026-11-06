import Mathlib

theorem algebra_15690 (x : ℝ) (h : x = 60 / 30) :
    (70 * 3 / x) = 105 := by 
  rw [h]
  norm_num