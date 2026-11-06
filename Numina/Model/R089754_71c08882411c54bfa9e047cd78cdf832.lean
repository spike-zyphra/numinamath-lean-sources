import Mathlib

theorem algebra_96247 (a : ℝ) (ha : a ≠ 0) (ha1 : a = -2) :
    max (max (max (max (4 * a) (-3 * a)) (24 / a)) (a ^ 2)) 1 = 6 := by 
  rw [ha1]
  norm_num [max_eq_right, max_eq_left]
  all_goals norm_num