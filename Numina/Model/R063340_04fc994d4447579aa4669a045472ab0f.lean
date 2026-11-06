import Mathlib

theorem algebra_95825 {a : ℝ} (ha : a ≠ 0) (h : a = 1 / 2) :
    (2 / a + 1 / (2 * a)) / a = 10 := by 
  rw [h]
  norm_num